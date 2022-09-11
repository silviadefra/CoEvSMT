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

