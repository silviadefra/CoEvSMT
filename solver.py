#!/usr/bin python3

from z3 import *
from multiprocessing import Process
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np
import math
import pandas as pd
from threading import Lock
import random
import time
import argparse
import logging
from sys import exit
from io import StringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
import itertools

# Parametri per l'algoritmo: vanno passati da linea di comando
smt_spec = ""
num_species=2
num_pop=2


# Informazioni sulla specifica: possono essere estratte dal file SMT
num_var=2
X=IntVector('x',num_var)
F=[X[0] > 2, X[0] < 2, X[1] < 10]
F_split=np.array_split(F, num_species)
d={'formula':F_split, 'vector': [None]*num_species, 'population':[[None]*num_pop]*num_species}
data=pd.DataFrame(data=d)



###
# This function ...
###
def thread_z3sol(index,s): # perché `thread`?
    #s=Solver()
    global data
    # CON LA RIGA SOTTO PUOI CARICARE DIRETTAMENTE UNA SPECIFICA SMT DA STRINGA
    # s.add(z3.parse_smt2_string(smt_spec))
    s.add(list(data.at[index,'formula']))
    if s.check()==unsat:
        raise ValueError("no solution exists")
    data.at[index,'vector']=[s.model()[i].as_long() for i in X]
    data.at[index,'vector']=[0 if i==None else i for i in data.at[index,'vector']]
    return 5 # TODO: perché 5?

###
# This function ...
###
def check_sat(s,index,lock):
    global data
    list_kill_futures=[]
    for i in list(data.index.values):#la lista si modifica? altrimenti prob, comunque prob se legge questa riga e dopo i viene eliminato da altro thread
        if i==index:
            continue
        if s.check([X[j]==data.at[i,'vector'][j] for j in range(num_var)])==sat:
            with lock:
                s.add(list(data.at[i,'formula']))
                data.at[index,'formula']=np.append(data.at[index,'formula'],data.at[i,'formula'])
                data.at[index,'vector']=data.at[i,'vector']
                data=data.drop(i)
            list_kill_futures.append(i) #non necessario, basta non riattivare i threads
    return list_kill_futures

###
# This function ...
###
def neighbor(index):
    global data
    dif=[100]*num_species #da vedere il 100
    for i in list(data.index.values):
        if i==index:
            continue
        subtracted = [abs(x - y) for (x,y) in zip(data.at[index,'vector'],data.at[i,'vector'])]
        dif[i]=sum(subtracted)
    my_neighbor_dif=min(dif)
    my_neighbor=dif.index(my_neighbor_dif)
    return zip(my_neighbor,my_neighbor_dif)

###
# This function ...
###
def genetic_alg(index,my_neighbor):
    global data
    generation=0
    best_fitness=my_neighbor[1]
    animal=[format(element1,'b').zfill(16) for element1 in data.at[index,'vector']]
    data.at[index, 'population']=[animal]*num_pop
    population=[animal,best_fitness]*num_pop        #data.at[index, 'population']=[animal]*num_pop
    while best_fitness > 0 and generation < 1000:
        new_population = [None]*num_pop
        my_parent1= min(random.sample(population,2), key=lambda individual: individual[1])[0]#my_parent=random.sample(data.at[index, 'population'],2)  #best fitness da fare
        my_neighbor_parent=random.choice(data.at[my_neighbor[0],'population'])
        if random.random() < 0.7:
            pos=randrange(16)
            my_parent2=my_parent1[:pos]+my_neighbor_parent[pos:]
            my_parent1=my_neighbor_parent[:pos]+my_parent1[pos:]
        for i in range(16):
            if random.random()<0.3:
                #TODO: cambiare bit in pos i
                pass

###
# This function ...
###
def run():
    with ThreadPoolExecutor() as executor:
        solvers=[None]*num_species
        futures=[None]*num_species
        for i in range(num_species):
            solvers[i] = Solver()
            futures[i] = executor.submit(thread_z3sol, i, solvers[i])
        for future in as_completed(futures):
            if future.cancelled():
                continue
            try:
                print(future.result())
            except ValueError as e:
                logging.error(e)
                executor.shutdown(wait=False, cancel_futures=True)
                exit()
        #test da qui in poi
        lock=Lock()
        futures=[executor.submit(check_sat,solvers[i],i,lock) for i in range(num_species)]
        for future in futures:
            if not future.result():
                for i in future.result():
                    futures[i].shutdown(wait=False)
        species_alive=data.index.values
        if len(species_alive)==1:
            print(data.loc[species_alive])
            exit()
        futures=[executor.submit(neighbor,i) for i in list(species_alive)]
        for future in futures: print(future.result())


########################
# CODICE VECCHIO SOPRA #
########################


###
# This function takes a SMT specification and splits it into N sub specitications returned as a list
###
def parse_and_split(smt_spec, n):

    parser = SmtLibParser()
    script = parser.get_script(StringIO(smt_spec))

    print(script)

    preamble_segment = extract_preamble(script)
    logging.debug("SMT preamble extracted")
    print(preamble_segment)

    assertion_blocks = split_assertions(script, n)
    logging.debug("SMT assertion blocks extracted")
    print(assertion_blocks)

    sub_script_list = []
    for i in range(n):
        sub_script = SmtLibScript()
        for p in preamble_segment:
            sub_script.add_command(p)
        for a in assertion_blocks[i]:
            sub_script.add_command(a)
        sub_script_list.append(sub_script)

    return sub_script_list

###
# This function takes a SMT specification and returns its preamble (without the assertions)
###
def extract_preamble(script):

    set_logic = script.filter_by_command_name("set-logic")
    decl_consts = script.filter_by_command_name("declare-const")
    # Only constants for now
    # decl_funs = script.filter_by_command_name("declare-fun")

    return itertools.chain(set_logic, decl_consts)

###
# This function takes a SMT specification and returns the assertions splited into N sub assertions
###
def split_assertions(script, n):

    assertions = script.filter_by_command_name("assert")

    assertion_blocks = []

    for b in range(n):
        assertion_blocks.append([])

    i = 0
    for a in assertions:
        assertion_blocks[i%n].append(a)
        i += 1

    return assertion_blocks

###
# This function solves a list of specs and returns a list of models (one for each spec).
# Model i in the returned list is None if spec is is UNSAT.
###
def solve_specs(specs):

    models = []

    # TODO: the following loop should be parallelized
    for script in specs:
        stream = StringIO()
        script.serialize(stream)
        formula = stream.read()

        ### TEMP CODE: ripuliamo il file dalle () extra
        formula.replace(" ()", "")
        ### FINE TEMP CODE

        solver = z3.Solver()
        solver.from_string(formula)
        solver_response = solver.check()

        if solver_response == sat:
            model = solver.model()
            models.append(model)
        else:
            print(solver_response)
            exit()

    return models

###
# This function creates one population from each model in *models*
###
def initialize_populations(models):
    for m in models:
        print(m)

    return []

###
# This function returns true when the computation is over
###
def stop_condition(populations):
    # TODO: TBI
    return True

###
# This function applies crossover and mutation to each population in *populations*.
# Returns a new list of populations
###
def cross_and_evolve(populations):
    # TODO: TBI
    return []

###
# This function eliminates the worst individuals
###
def select_fittests(populations):
    # TODO: TBI
    return []

###
# This function returns (i,j) if populations i and j collide (the have a common individual). (None, None) otherwise
###
def population_collision(populations):
    # TODO: TBI
    return None, None

###
# This function returns a list of populations where population i and j have been merged
###
def merge_populations(populations, i, j):
    # TODO: TBI
    return []



###
# Main function
###
def main():

    # parse arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("smt", type=str, help='input SMT specification') # SMT file
    parser.add_argument("--species", type=int, help='initial number of species') #Default potrebbe essere uguale al numero dei processori disponibili, oppure 2
    parser.add_argument("--population", type=int, help='initial number of individuals for each species') #Default potrebbe essere 2
    parser.add_argument("--file", action='store_true', help='If set, smt specification is retrieved from file') #Default: false
    args = parser.parse_args()

    global smt_spec, num_species, num_pop

    if args.file:
        file = open(args.smt, "r")
        smt_spec = file.read()
        file.close()
    else:
        smt_spec = args.smt

    if args.species:
        num_species = args.species_alive

    if args.population:
        pop_size = args.population

    ### Main algorithm
    logging.info("Beginning")

    # STEP 1: parse *SMT specification* and split it into *N* smaller *SMT specifications*
    sub_specs = parse_and_split(smt_spec, num_species)

    # STEP 2: solve the *N SMT specifications* and finds *N models* (otherwise *UNSAT*)
    models = solve_specs(sub_specs)

    # STEP 2.1: if exists i in models s.t. models[i] == None --> return UNSAT.
    for m in models:
        if m == None:
            logging.info("UNSAT model " + m)
            exit()

    # STEP 3: initialize *N populations* with the *N models*
    populations = initialize_populations(models)

    # STEP 4: repeat until *stop condition*
    while not stop_condition(populations):

        # STEP 5: Parallel crossover and mutation
        new_populations = cross_and_evolve(populations)

        # STEP 6: Parallel selection (based on *fitness function*)
        new_populations = select_fittests(new_populations)

        # STEP 7: If 2 populations collide: merge
        pop_i, pop_j = population_collision(populations)
        if not pop_i is None:
            new_populations = merge_populations(new_populations, pop_i, pop_j)

        populations = new_populations

    logging.info("End")

# Così lo rendiamo eseguibile
if __name__ == "__main__":
    logging.basicConfig(format='[+] %(asctime)s %(levelname)s: %(message)s', level=logging.DEBUG)
    main()
