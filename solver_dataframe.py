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
from pysmt.shortcuts import Solver, Equals, Int, And
import copy
import itertools
import pygad

# Parametri per l'algoritmo: vanno passati da linea di comando
smt_spec = ""
num_species=2
num_pop=8
literals = []
types=[]
smt_types=[]
data=None


###
# This function takes a SMT specification and splits it into N sub specitications returned as a list
###
def parse_and_split(smt_spec, n):

    parser = SmtLibParser()
    script = parser.get_script(StringIO(smt_spec))

    preamble_segment = extract_preamble(script)
    logging.debug("SMT preamble extracted")

    assertion_blocks = split_assertions(script, n)
    logging.debug("SMT assertion blocks extracted")

    sub_script_list = []
    sub_script_preamble = SmtLibScript()
    for p in preamble_segment:
        sub_script_preamble.add_command(p)
    for i in range(n):
        sub_script = SmtLibScript()
        for a in sub_script_preamble:
            sub_script.add_command(a)

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
# If a solver is unsat the function prints unsat
#This function creates the list of literals
###
def solve_specs(specs):

    models = []
    global literals
    global smt_types
    global data
    solvers=[]
    # TODO: the following loop should be parallelized
    for script in specs:
        solver = Solver(name="z3")
        log = script.evaluate(solver)
        # logging.debug(log)
        solver_response = solver.solve()
        solvers.append(solver)
 
        if solver_response:
            model = solver.get_model()
            models.append(model)

        else:
            print("unsat")       #problem with unknown
            exit()

    literals=list(solver.environment.formula_manager.get_all_symbols()) #returns the list of symbol names
    smt_types=[l.symbol_type() for l in literals]
    data['solver']=solvers
    return models

###
# This function creates one population from each model in *models* and the list of types
###
def initialize_populations(models):
    
    populations=[]
    neighbors=[]
    global literals
    global data 
    global types   

    # TODO: the following loop should be parallelized
    for m in models:
        individual=[m.get_py_value(i) for i in literals]
        populations.append([individual]*num_pop)  #each population is made up of *num_pop* equal individuals
        neighbors.append(individual)   

    types=[type(i) for i in individual]  #returns the list of types
    random.shuffle(neighbors)   
    data['neighbor']=neighbors #from data['neighbor'] we get one parent for the genetic alg, initially it is chosen randomly 
    data['population']=populations
    
    return 0

###
# This function returns true when the computation is over
###
def stop_condition():

    return len(data.index.values)==1


###
# This function applies a genetic algorithm to each population in *populations*.
###
def genetic_algorithm():
 
    global data



    # TODO: the following loop should be parallelized
    for i in list(data.index.values):
        solver=data.at[i,'solver']
        index=i
        
###
# This function takes an individual and returns his fitness, considering if he is a solution of the relative solver.
###

        def fitness_func(individual,ind):
            global data
            formula=And([Equals(x,Int(y)) for (x,y) in zip(literals, individual)]) #formula=And([Equals(x,z(y)) for (x,z,y) in zip(literals, smt_types, individual)]) 
            if not solver.is_sat(formula):
                fitness=- math.inf
            
            else:
                fitness_list=[]
                for i in list(data.index.values):
                    if i==index:
                        continue
                  
                    valid_fitness=[]
                    for p,f in zip(data.at[i,'population'],data.at[i,'fitness']):
                        if f!= -math.inf:   
                            valid_fitness.append([np.linalg.norm((individual - p), ord=1),p])
                    
                    fitness_i = min(valid_fitness, key=lambda item: item[0])
                    if fitness_i[0]==0:
                        data.at[index,'merge']=i
                    fitness_i[0]=-1*fitness_i[0]
                    fitness_list.append(fitness_i)
                best=max(fitness_list, key=lambda item: item[0])
                data.at[index,'neighbor'] = best[1]
                fitness = best[0]
                
            #logging.debug("Fitness of {ind}: {fit}".format(ind=individual, fit=fitness))
            return fitness

        def parent_selection_func(fitness, num_parents, ga_instance):
            global num_pop,data
            
            (parents,indices) = ga_instance.steady_state_selection(fitness[:num_pop-1],num_parents-1)
            parents=np.concatenate((parents,[data.at[index,'neighbor']]),axis=0)
            indices=np.insert(indices,num_parents-1,[num_pop-1])
            return parents, indices

        #def on_gen(ga):
            #logging.debug("Generation {num_gen}".format(num_gen=ga.generations_completed))
            #logging.debug(ga.population)

        
        fitness_function = fitness_func 

        num_generations =1
        num_parents_mating = math.ceil(num_pop/2)
        
        probability=0.5
        if random.random() < probability:
            min_pos=data.at[index,'fitness'].index(min(data.at[index,'fitness']))
            initial_population=data.at[index,'population'][:min_pos]+ data.at[index,'population'][min_pos+1:]
            initial_population.append(data.at[index,'neighbor'])
            parent_selection_type =parent_selection_func
        else:
            initial_population=data.at[index,'population']
            parent_selection_type ="sss"

        num_genes=len(types)
        gene_type=types.copy() 
 
        keep_elitism=math.ceil(num_pop/4)

        crossover_type = "single_point" 

        mutation_type = "random"        
        random_mutation_min_val=-2
        random_mutation_max_val=2
        mutation_probability= 0.1

        stop_criteria= "reach_0"
        save_solutions=True
        allow_duplicate_genes=False
        #on_generation=on_gen

        ga_instance = pygad.GA(num_generations=num_generations,
                       num_parents_mating=num_parents_mating,
                       fitness_func=fitness_function,
                       initial_population=initial_population,
                       num_genes=num_genes,
                       gene_type=gene_type,
                       stop_criteria=stop_criteria,
                       parent_selection_type=parent_selection_type,
                       random_mutation_min_val=random_mutation_min_val,
                       random_mutation_max_val=random_mutation_max_val,
                       crossover_type=crossover_type,
                       keep_elitism=keep_elitism,
                       #keep_parents=keep_parents,
                       #allow_duplicate_genes=allow_duplicate_genes,
                       #on_generation=on_generation,
                       mutation_type=mutation_type,
                       mutation_probability=mutation_probability)
        ga_instance.run()
        
        solution, solution_fitness, solution_idx = ga_instance.best_solution()
        #logging.debug("Population {pop}: Parameters of the best solution : {solution}".format(solution=solution,pop=index))
        #logging.debug("Population {pop}: Fitness value of the best solution = {solution_fitness}".format(solution_fitness=-solution_fitness,pop=index))
        
        data.at[index,'population']=[list(p) for p in ga_instance.population]
        data.at[index,'fitness']=list(ga_instance.last_generation_fitness)
    return solution



###
# This function merges populations i and j 
###
def merge_populations(i, j):
    
    global data

    for a in data.at[j,'solver'].assertions:
        data.at[i,'solver'].add_assertion(a)
    data.at[i,'merge']=None
    data=data.drop(j)

    return 0



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

    global smt_spec, num_species, num_pop, data

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
    
    t=time.time()
    
    
    d={'merge':[None]*num_species,'fitness':[[0]*num_pop]*num_species}
    data=pd.DataFrame(data=d)

    # STEP 1: parse *SMT specification* and split it into *N* smaller *SMT specifications*
    sub_specs = parse_and_split(smt_spec, num_species)

    # STEP 2: solve the *N SMT specifications* and finds *N models* (otherwise *UNSAT*)
    models = solve_specs(sub_specs)

    # STEP 3: initialize *N populations* with the *N models*
    initialize_populations(models)
    j=0
    # STEP 4: repeat until *stop condition*
    #while not stop_condition():

        # STEP 5: Parallel genetic algorithm (based on *fitness function*)
    solution=genetic_algorithm()

        # STEP 6: If 2 populations collide: merge
        #for i in list(data.index.values):
            #if data.at[i,'merge'] is not None:
                #merge_populations(i,data.at[i,'merge'])
                #break
        #j+=1
    output = []
    for l,s in zip(literals, solution):
        output.append("{lit}={sol}".format(lit=l,sol=s))
    f=open("solutions.txt","a")
    f.write("Generation: {num_gen}\n".format(num_gen=j))
    f.write("Solution: [" + ", ".join(str(x) for x in output) + "]\n")
    f.write("Time: {time}\n".format(time=time.time()-t))
    f.close()
    logging.info("End")

# Così lo rendiamo eseguibile
if __name__ == "__main__":
    logging.basicConfig(format='[+] %(asctime)s %(levelname)s: %(message)s', level=logging.DEBUG)
    main()
