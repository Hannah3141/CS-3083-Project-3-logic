import numpy as np
import matplotlib.pyplot
import os
import time
import itertools
import re
import math

# Test your function first with these manually entered KB-alpha pairs
KB1 = {"X2|!X1", "X1"}
Alpha1 = {"X2"}

KB2 = {"B|!A", "A", "!B|!A|C"}
Alpha2 = {"C", "B|A"}

KB3 = {"!Burglar|Alarm", "!Earthquake|Alarm", "!Alarm|JohnCall", "!Alarm|MaryCall"}
Alpha3 = {"!Burglar|JohnCall", "!Burglar|MaryCall"}

KB4 = {'X2', 'X2|X3', '!X3|!X2', '!X1', '!X1|X2'}
Alpha4 = {'X3'}

KB5 = {'X2', 'X1|X7|X4|X5|!X10|!X8|!X3|X9|!X2', '!X7|X4|X8|X3|!X6|X1|X10', 'X1|X5|!X2|X4|X7|!X10|!X3', 'X9|X5|X4|!X3|X1', '!X7|X6|X10|X3|X2|X4', 'X9|X3|X8|X10|X6|X4|!X7|X5|X1', 'X1|!X6|X2|X10|X5', 'X5|!X1|X3|X4', 'X5|X9|X3|!X7|!X6', '!X6|X2|!X1|X8', '!X5|X6|!X4|X9|X1|X10|X2|X3|!X7', 'X5|X7|!X8|!X3|!X1', 'X10|!X4', '!X7|!X3|!X9|!X1', 'X4|X6|X1|X7|X10', '!X8|X3|!X2', '!X8|!X6|X10|!X1|!X9|X2', 'X2|!X4|X8', 'X3|X1|!X7|X5|X9|!X4|X2|!X10|X6'}
Alpha5 = {'X10|!X3', '!X1'}


# A random KB-alpha pair generator
# Call this function to create bigger problems to evaluate your functions
# n: total number of variables in KB and alpha
# m_kb: the number of disjunctive clauses in the KB
# m_alpha: the number of disjunctive clauses in the query
# p: the probability of having negated literals
def kbq_gen(n=3, m_kb=6, m_alpha=1, p=0.3):
    assignment = np.random.choice([True, False], n)
    kb = set()
    kb_std = set()
    for i in range(m_kb):
        while True:
            lcnt = np.random.randint(1, n)
            vars = np.random.choice(np.arange(n)+1, lcnt, replace=False)
            polarity = np.random.choice(["", "!"], len(vars), p=[1-p, p])
            res = False
            for j in range(lcnt):
                if polarity[j]=="!": res = res or not assignment[vars[j]-1]
                else: res = res or assignment[vars[j]-1]
            if res:
                literals = [polarity[i]+"X"+str(vars[i]) for i in range(len(vars))]
                if "|".join(np.sort(np.array(literals))) not in kb_std:
                    kb.add("|".join(literals))
                    kb_std.add("|".join(np.sort(np.array(literals))))
                    break
    alpha = set()
    alpha_std = set()
    for i in range(m_alpha):
        while True:
            lcnt = np.random.randint(1, n)
            vars = np.random.choice(np.arange(n)+1, lcnt, replace=False)
            polarity = np.random.choice(["", "!"], len(vars), p=[1-p, p])
            literals = [polarity[i]+"X"+str(vars[i]) for i in range(len(vars))]
            if "|".join(np.sort(np.array(literals))) not in alpha_std:
                alpha.add("|".join(literals))
                alpha_std.add("|".join(np.sort(np.array(literals))))
                break
    return kb, alpha

# Function to prove entailment using the resolution rule
# Return True if KB entails alpha, False otherwise. 
def PL_resolution_entail(KB, alpha):
    kb = organize(KB)
    a = organize(alpha)
    for clause in a:
        for var in clause:
            newTuple = (var[0], not var[1])
            newSet = set()
            newSet.add(newTuple)
            kb.append(newSet)
    new = set()
    while True:
        for i in range(len(kb)):
            for j in range(i + 1, len(kb)):
                c1 = kb[i].copy()
                c2 = kb[j].copy()
                resolvents = plResolve(c1, c2)
                for r in resolvents:
                    if r != None:
                        if set() == r: 
                            return True
                        new.add(tuple(r)) 
        numNew = 0
        for r in new:
            s = set(r)
            if s not in kb: 
                numNew = numNew + 1 #TODO: surely there is a better way
                kb.append(s)
        if numNew == 0:
            return False

def organize(KB):
    kb = []
    for sent in KB:
        clause = set()
        literals = sent.split("|")
        for literal in literals:
            if literal[0] == "!":
                clause.add((literal[1:], 0)) 
            else:
                clause.add((literal, 1))
        kb.append(clause)
    return kb

def plResolve(clause1, clause2):
    ret = []
    for var in clause1:
        if (var[0], not var[1]) in clause2:
            temp1 = clause1.copy()
            temp2 = clause2.copy()
            temp1.remove(var)
            temp2.remove((var[0], not var[1]))
            for each in temp2:
                temp1.add(each)
            ret.append(temp1) #will only return none if both are empty, which is i think what we want
    return ret
# Function to prove entailment using the DPLL algorithm
# Return True if KB entails alpha, False otherwise
def DPLL_entail(KB, alpha):
    kb = organize(KB)
    a = organize(alpha)
    #negate alpha
    for clause in a:
        for var in clause:
            newTuple = (var[0], not var[1])
            newSet = set()
            newSet.add(newTuple)
            kb.append(newSet)
    symbols = [] # the variables that are not assigned yet, i wish i could do this with one list instead of both models and symbols
    for clause in kb:
        for var in clause:
            if var[0] not in symbols:
                symbols.append(var[0])
    return DPLL(kb, symbols, {})

def DPLL(kb, symbols, model):
    if len(symbols) == 0:
        for each in kb: #TODO: the model will hold the assignments, we'll have to actually plug them in
            if len(each) == 0: 
                return True
        return False #if the model is full and none of them are false or unsatisfiable, the model is true, so the entailment is false
    pureList = findPureSymbol(kb, symbols)
    if pureList != None:
        model[pureList[0]] = pureList[1]
        symbols.remove(pureList[0])
        updateKB(kb, pureList)
        return DPLL(kb, symbols, model)
    
    unitList = findUnitClause(kb, symbols)
    if unitList != None:
        model[unitList[0]] = unitList[1]
        symbols.remove(unitList[0])
        updateKB(kb, unitList)
        return DPLL(kb, symbols, model)
    next = symbols.pop()
    newModel1 = model.copy()
    newModel1[next] = True
    newModel2 = model.copy()
    newModel2[next] = False
    return DPLL(kb, symbols, newModel1) or DPLL(kb, symbols, newModel2)

def findPureSymbol(kb, symbols, i=0): #TODO: could do the same with not in model
    if i >= len(symbols):
        return None
    symbol = symbols[i]
    initialValue = None
    for clause in kb:
        for var in clause:
            if type(var) != bool and symbol == var[0]:
                initialValue = var[1]
                break #idk how else to set initialValue the first time
        if initialValue != None:
            break
    for clause in kb:
        for var in clause:
            if type(var) != bool and symbol == var[0]:
                if var[1] != initialValue:
                    return findPureSymbol(kb, symbols, i+1)
    return [symbol, initialValue]
        
def findUnitClause(kb, symbols):
    for clause in kb:
        if len(clause) == 1:
            for var in clause: #only way to access a set is by iterating
                if type(var) != bool and var[0] in symbols:
                    return var
    return None

def updateKB(kb, assignment):
    for i in range(len(kb)): #update kb
        toDelete = []
        for var in kb[i]:    
            if type(var) != bool:
                if assignment[0] == var[0]:
                    if assignment[1] == var[1]:
                        kb[i] = {True} #if any one variable is true, the whole clause is true
                    else:
                        toDelete.append(var) #if a variable is false, its not useful so we can get rid of it
        for each in toDelete:
            kb[i].remove(each)

kb = KB4
a = Alpha4
print(">>KB")
print(kb)
print(">>Alpha")
print(a)
print("Entailment is", PL_resolution_entail(kb, a))
print("Entailment is", DPLL_entail(kb, a))

print("---------------------------")


pltimesxNumvars = []
results = []
dplltimesxNumvars = []
for l in range(5):
    print(l)
    for i in range(3, 7):
        myKB, myAlpha = kbq_gen(i, 11, 2) # try more options, like (10, 20, 2), (3, 5, 1), etc. (4, 6, 2)

        '''start = time.time()
        plresult = PL_resolution_entail(myKB, myAlpha)
        pltimesxNumvars.append((i, time.time() - start))

        start = time.time()
        dpllresult = DPLL_entail(myKB, myAlpha)
        dplltimesxNumvars.append((i, time.time() - start))

        results.append((plresult, dpllresult))'''
        print("Entailment is", PL_resolution_entail(myKB, myAlpha))
        print("Entailment is", DPLL_entail(myKB, myAlpha))
'''
print(pltimesxNumvars)
print(dplltimesxNumvars)
x = []
for each in pltimesxNumvars:
    x.append(each[0])
y = []
for each in pltimesxNumvars:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)

x = []
for each in dplltimesxNumvars:
    x.append(each[0])
y = []
for each in dplltimesxNumvars:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)
#matplotlib.pyplot.plot(results)
matplotlib.pyplot.show()

'''
pltimesxSizekb = []
dplltimesxSizekb = []
for l in range(5):
    print(l)
    for i in range(1, 50, 5):
        myKB, myAlpha = kbq_gen(4, i, 2) # try more options, like (10, 20, 2), (3, 5, 1), etc. (4, 6, 2)
        print("Entailment is", PL_resolution_entail(myKB, myAlpha))
        print("Entailment is", DPLL_entail(myKB, myAlpha))
'''
        start = time.time()
        plresult = PL_resolution_entail(myKB, myAlpha)
        pltimesxSizekb.append((i, time.time() - start))

        start = time.time()
        dpllresult = DPLL_entail(myKB, myAlpha)
        dplltimesxSizekb.append((i, time.time() - start))

print(pltimesxSizekb)
print(dplltimesxSizekb)
x = []
for each in pltimesxSizekb:
    x.append(each[0])
y = []
for each in pltimesxSizekb:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)

x = []
for each in dplltimesxSizekb:
    x.append(each[0])
y = []
for each in dplltimesxSizekb:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)
matplotlib.pyplot.show()
'''
pltimesxSizea = []
dplltimesxSizea = []
for l in range(5):
    print(l)
    for i in range(1, 7):
        myKB, myAlpha = kbq_gen(4, 11, i) # try more options, like (10, 20, 2), (3, 5, 1), etc. (4, 6, 2)
        print("Entailment is", PL_resolution_entail(myKB, myAlpha))
        print("Entailment is", DPLL_entail(myKB, myAlpha))
'''
        start = time.time()
        plresult = PL_resolution_entail(myKB, myAlpha)
        pltimesxSizea.append((i, time.time() - start))

        start = time.time()
        dpllresult = DPLL_entail(myKB, myAlpha)
        dplltimesxSizea.append((i, time.time() - start))


print(pltimesxSizea)
print(dplltimesxSizea)
x = []
for each in pltimesxSizea:
    x.append(each[0])
y = []
for each in pltimesxSizea:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)

x = []
for each in dplltimesxSizea:
    x.append(each[0])
y = []
for each in dplltimesxSizea:
    y.append(each[1])
matplotlib.pyplot.plot(x, y)
#matplotlib.pyplot.plot(results)
matplotlib.pyplot.show()'''