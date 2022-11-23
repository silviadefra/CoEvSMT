#!/usr/bin python3

from z3 import *
from multiprocessing import Manager, cpu_count
from concurrent.futures import ProcessPoolExecutor, as_completed
import numpy as np
import math
import random
import time
import argparse
import logging
from sys import exit
from io import StringIO
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.shortcuts import Solver, Equals, Int, And, Real, Bool
import itertools
import pygad
import csv

# Parametri per l'algoritmo: vanno passati da linea di comando
smt_spec = ""
num_pop=8
num_gen=2000
distance=0
num_proc=cpu_count()
mut_prob=0.1
neig_prob=0.5

###
# This function takes a SMT specification and splits it into N sub specitications returned as a list
###
def parse_and_split(smt_spec, n):

    parser = SmtLibParser()
    script = parser.get_script(StringIO(smt_spec))

    preamble_segment,literals  = extract_preamble(script)
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
    
    return sub_script_list,literals


###
# This function takes a SMT specification and returns its preamble (without the assertions)
###
def extract_preamble(script):

    set_logic = script.filter_by_command_name("set-logic")
    decl_consts = script.filter_by_command_name("declare-const")
    
    # Only constants for now
    #decl_funs = script.filter_by_command_name("declare-fun")
    literals=[l.args[0] for l in decl_consts]


    return itertools.chain(set_logic, decl_consts), literals

###
# This function takes a SMT specification and returns the assertions splited into N sub assertions
###
def split_assertions(script, n):

    assertions = script.filter_by_command_name("assert")
    data = [ (random.random(), line) for line in assertions ] #shuffle
    data.sort()
    assertion_blocks = []


    for b in range(n):
        assertion_blocks.append([])

    i = 0
    for _, a in data:
        assertion_blocks[i%n].append(a)
        i += 1

    return assertion_blocks

###
# This function solves a spec and returns a solution.
# If the Model is UNSAT, this function prints unsat.
###
def solve_specs(spec,literals):
    solver = Solver(name="z3")
    spec.evaluate(solver)
    solver_response = solver.solve()
 
    if solver_response:
        model = solver.get_model()
        individual=[model.get_py_value(i) for i in literals]

    else:
        individual="unsat"

    return individual

###
# This function returns true when the computation is over
###
def stop_condition(num_species,j,num_gen):

    if j==num_gen:
        return True
    return num_species==1

###
# This function applies crossover and mutation to each population in *populations*.
# Returns a new list of populations
###
def genetic_algorithm(index,pop,spec,num_species,fit,neighbor,literals,mut_prob,neig_prob):

    solver= Solver(name="z3")
    spec.evaluate(solver)
    types=[type(i) for i in pop[0][0]]  #returns the list of types
    list_functions=[Int if i==int else Real if i==float else Bool for i in types] #TODO   
###
# This function takes an individual and returns his fitness, considering if he is a solution of the relative solver.
###

    def fitness_func(individual,ind):

        global merge,neig
        merge=None
        neig=neighbor
        formula=And([Equals(x,z(y)) for (x,y,z) in zip(literals, individual,list_functions)]) 
        if not solver.is_sat(formula):
                fitness=- math.inf
            
        else:
            fitness_list=[]
            for i in range(num_species):
                if i==index:
                    continue
                  
                valid_fitness=[]
                for p,f in zip(pop[i],fit[i]):
                    if f!= -math.inf:   
                        valid_fitness.append([np.linalg.norm((individual - p), ord=1),p])
                    
                fitness_i = min(valid_fitness, key=lambda item: item[0])
                if fitness_i[0]==0:
                    merge=i
                fitness_i[0]=-1*fitness_i[0]
                fitness_list.append(fitness_i)
            best=max(fitness_list, key=lambda item: item[0])
            neig = best[1]
            
            fitness = best[0]
                
            #logging.debug("Fitness of {ind}: {fit}".format(ind=individual, fit=fitness))
        return fitness
    

    def on_gen(ga):
        #TODO
        #logging.debug(ga.last_generation_fitness)
        #pop[index]=[list(p) for p in ga.population] 
        pop[index]=ga.population.copy()
        fit[index]=list(ga.last_generation_fitness) #changeit

    

    def crossover_func(parents, offspring_size, ga):

        global neig
        if random.random() < neig_prob:
            parents=np.concatenate((parents,[neig]),axis=0)
            
        offspring=ga.single_point_crossover(parents,offspring_size)

        return offspring

        
    
    initial_population=pop[index]        
    num_generations =500  #TODO
    fitness_function = fitness_func

    parent_selection_type ='sss'
    num_parents_mating = math.ceil(len(pop[index])/2)
    keep_elitism=math.ceil(len(pop[index])/4)

    num_genes=len(types)
    gene_type=types
    on_generation=on_gen

    crossover_type = crossover_func

    mutation_type = "random"        
    random_mutation_min_val=-2
    random_mutation_max_val=2
    mutation_probability= mut_prob

    stop_criteria= "reach_0"

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
                       on_generation=on_generation,
                       mutation_type=mutation_type,
                       mutation_probability=mutation_probability)
    ga_instance.run()

    solution, solution_fitness, solution_idx = ga_instance.best_solution()
    #logging.debug("Population {pop}: Parameters of the best solution : {solution}".format(solution=solution,pop=index))
    #logging.debug("Population {pop}: Fitness value of the best solution = {solution_fitness}".format(solution_fitness=-solution_fitness,pop=index))
    return merge,index,neig, solution


###
# This function returns a list of populations where population i and j have been merged
###
def merge_populations(fit,pop,specs, to_merge):
    to_keep=[]
    for pair in to_merge:
        if pair[0] in to_keep or pair[1] in to_keep:
            continue
        to_keep.extend(pair)
        for a in specs[pair[0]].filter_by_command_name('assert'):
            specs[pair[1]].add_command(a)
    to_kill=to_keep[0::2]
    new_specs=[elem for i,elem in enumerate(specs) if i not in to_kill]
    new_pop=[elem for i,elem in enumerate(pop) if i not in to_kill]
    new_fit=[elem for i,elem in enumerate(fit) if i not in to_kill]
    return new_fit,new_pop, new_specs,



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
    parser.add_argument("--generations", type=int, help='maximum number of generations to stop')
    parser.add_argument("--mutation", type=int, help='probability of selecting a gene for applying the mutation operation')#Default 0.1
    parser.add_argument("--neighbor", type=int, help='probability of selecting a parent from the neighbor population') #Default 0.5
    args = parser.parse_args()

    global smt_spec, num_pop, num_gen, distance, num_proc, mut_prob, neig_prob
    smt_spec = args.smt

    if args.file:
        file = open(args.smt, "r")
        smt_spec = file.read()
        file.close()
    else:
        smt_spec = args.smt

    if args.species and args.species< num_proc:
        num_proc = args.species

    if args.population:
        num_pop = args.population

    if args.generations:
        num_gen=args.generations

    if args.mutation:
        mut_prob=args.mutation

    if args.neighbor:
        neig_prob=args.neighbor




    ### Main algorithm
    num_species=num_proc
    logging.info("Beginning")
    t=time.time()

    # STEP 1: parse *SMT specification* and split it into *N* smaller *SMT specifications*
    sub_specs,literals = parse_and_split(smt_spec, num_species)
    with ProcessPoolExecutor(num_proc) as executor:

        # STEP 2-3: solve the *N SMT specifications* and finds *N models* (otherwise *UNSAT*) and initialize *N populations* with the *N models*
        populations =[]
        neighbors=[]
        for result in executor.map(solve_specs,sub_specs,itertools.repeat(literals)):
            if result=="unsat":
                print(result)
                t=time.time()-t
                final_result=[args.smt,num_proc,num_pop,num_gen,mut_prob,neig_prob,result,t] #chiedere num_gen max o quelle fatte?
                with open("solutions.csv","a") as f:
                    writer = csv.writer(f)
                    writer.writerow(final_result)
                exit()
            populations.append([result]*num_pop)
            neighbors.append(result)
        random.shuffle(neighbors)

        mgr = Manager()
        populations = mgr.list(populations)
        fitness=mgr.list([[0]*num_pop]*num_species)
        #lock=mgr.Lock()

        j=0   
        # STEP 4: repeat until *stop condition*
        while not stop_condition(num_species,j,num_gen):

            # STEP 5: Parallel genetic algorithm (based on *fitness function*)
            futures=[executor.submit(genetic_algorithm,i,populations,sub_specs[i],num_species,fitness,neighbors[i],literals,mut_prob,neig_prob) for i in range(num_species)]

            to_merge=[]
            best_sol=[None]*num_species
            for future in as_completed(futures):
                (pop_i,pop_j,new_neighbor,best)=future.result()
                neighbors[pop_j]=new_neighbor
                best_sol[pop_j]=best

                if pop_i is not None:
                    to_merge.append([pop_i,pop_j])

            # STEP 6: If 2 populations collide: merge
            if to_merge:
                (fitness,populations,sub_specs)=merge_populations(fitness,populations,sub_specs,to_merge)
                num_species=len(populations)

            j+=1
            logging.debug("Time: {time}, Fitness: {fit}, Num gen: {gen}".format(time=time.time()-t,fit=fitness,gen=j*500))
            
        executor.shutdown()
    
    if num_species==1:
        output="sat"
    else:
        output="unknown"
    t=time.time()-t
    num_gen=j*500
    final_result=[args.smt,num_proc,num_pop,num_gen,mut_prob,neig_prob,output,t]
    with open("solutions.csv","a") as f:
        writer = csv.writer(f)
        writer.writerow(final_result)
       
    best_output = []
    for solution in best_sol:
        a=[]
        for l,s in zip(literals, solution):
            a.append("{lit}={sol}".format(lit=l,sol=s))
        best_output.append(a)
    logging.debug("Fitness: {fit}".format(fit=fitness))     
    logging.debug("Solution: [" + ", ".join(str(x) for x in best_output) + "]\n")
    logging.info("End")

# Così lo rendiamo eseguibile
if __name__ == "__main__":
    logging.basicConfig(filename='solutions.log', encoding='utf-8', level=logging.DEBUG)
    #logging.basicConfig(format='[+] %(asctime)s %(levelname)s: %(message)s', level=logging.DEBUG)
    main()

