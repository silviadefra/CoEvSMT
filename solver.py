#!/usr/bin python3

from z3 import *
from multiprocessing import Process
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np
import math
import pandas as pd
from threading import Lock
import time
import argparse
import logging
from sys import exit


# Parametri per l'algoritmo: vanno passati da linea di comando
smt_spec = ""
num_species=2
num_pop=2


# Informazioni sulla specifica: possono essere estratte dal file SMT
num_var=2
X=IntVector('x',num_var)
F=[X[0] > 2, X[0] < 2, X[1] < 10]
F_split=np.array_split(F, num_species)
d={'formula':F_split, 'vector': [None]*num_species}
data=pd.DataFrame(data=d)

def thread_z3sol(index,s):
    #s=Solver()
    global data
    s.add(list(data.at[index,'formula']))
    if s.check()==unsat:
        raise ValueError("no solution exists")
    data.at[index,'vector']=[s.model()[i] for i in X]
    data.at[index,'vector']=[0 if i==None else i for i in data.at[index,'vector']]
    return 5 # TODO: perché 5?

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


# In[5]:


def neighbor(index):
    global data
    dif=[100]*num_species #da vedere il 100
    for i in list(data.index.values):
        if i==index:
            continue
        for x,y in data.at[index,'vector'],data.at[i,'vector']:
            print(x)
            dif[i]=dif[i]+abs(x-y)
    print(dif)
    my_neighbor=dif.index(min(dif))
    print(min(dif))
    return my_neighbor


# In[12]:

def run():
    with ThreadPoolExecutor() as executor:
        solvers=[None]*num_species
        futures=[None]*num_species
        for i in range(num_species):
            solvers[i]=Solver()
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


def main():
    # parse arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("smt", type=str, help='input SMT specification') # SMT file
    parser.add_argument("--species", type=int, help='initial number of species') #Default potrebbe essere uguale al numero dei processori disponibili, oppure 2
    parser.add_argument("--population", type=int, help='initial number of individuals for each species') #Default potrebbe essere 2
    args = parser.parse_args()

    global smt_spec, num_species, num_pop
    smt_spec = args.smt

    if args.species:
        num_species = args.species_alive

    if args.population:
        pop_size = args.population

    logging.info("Beginning")
    run()
    logging.info("End")

# Così lo rendiamo eseguibile
if __name__ == "__main__":
    logging.basicConfig(format='[+] %(asctime)s %(levelname)s: %(message)s', level=logging.ERROR)
    main()
