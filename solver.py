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
from pysmt.shortcuts import Solver
import itertools

# Parametri per l'algoritmo: vanno passati da linea di comando
smt_spec = ""
num_species=2
num_pop=2


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
        sub_script = sub_script_preamble
        for a in assertion_blocks[i]:
            sub_script.add_command(a)
        sub_script_list.append(sub_script)
    #for i in range(n):  
        #sub_script = SmtLibScript()
        #for p in preamble_segment:
            #sub_script.add_command(p)
        #for a in assertion_blocks[i]:
            #sub_script.add_command(a)
        #sub_script_list.append(sub_script)
    
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

        solver = Solver(name="z3")
        log = script.evaluate(solver)
        # logging.debug(log)
        solver_response = solver.solve()

        if solver_response:
            model = solver.get_model()
            models.append(model)
        elif solver.is_unsat():
            print("unsat")
            exit()
        else:
            print("unknown")
            exit()

    return models

###
# This function creates one population from each model in *models*
###
def initialize_populations(models):

    # TODO: the following loop should be parallelized
    for m in models:
        #m=[m[i] for i in consts]
        logging.debug(m)

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
