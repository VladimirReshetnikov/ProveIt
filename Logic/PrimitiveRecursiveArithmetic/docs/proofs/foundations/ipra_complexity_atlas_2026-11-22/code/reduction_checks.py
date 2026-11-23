#!/usr/bin/env python3
"""Executable finite witnesses for report theorems N04 and N07--N21.

These are differential/exhaustive implementation checks, not Lean proofs and
not object-iPRA proof certificates. The 2SAT implementation materializes a
reachability table and is not claimed to use logarithmic work space.
Run with Python 3.10+: python3 code/reduction_checks.py
"""
from __future__ import annotations
from itertools import product, combinations, combinations_with_replacement
from random import Random
from collections import Counter
import json

# Literal +/- (i+1); a CNF retains its explicitly declared variable count.
def lit_value(lit, assignment):
    value = bool(assignment[abs(lit)-1])
    return value if lit > 0 else not value

def cnf_value(clauses, assignment):
    return all(any(lit_value(lit, assignment) for lit in c) for c in clauses)

def assignments(n):
    return product((False, True), repeat=n)

def sat_models(n, clauses):
    return [a for a in assignments(n) if cnf_value(clauses, a)]

# Circuit nodes 0..q-1 are inputs; subsequent gate arguments reference earlier
# nodes. Gates are ('const', bit), ('not', index), ('and'/'or', index,index).
def evaluate_circuit(q, gates, output, inputs):
    assert len(inputs) == q
    values = list(map(bool, inputs))
    for gate in gates:
        op, *args = gate
        if op == 'const': value = bool(args[0])
        elif op == 'not': value = not values[args[0]]
        elif op == 'and': value = values[args[0]] and values[args[1]]
        elif op == 'or': value = values[args[0]] or values[args[1]]
        else: raise ValueError(op)
        values.append(value)
    return values[output], tuple(values)

def tseitin(q, gates, output):
    clauses = []
    for idx, gate in enumerate(gates):
        z = q + idx + 1
        op, *args = gate
        if op == 'const': clauses.append((z if args[0] else -z,))
        elif op == 'not':
            a = args[0]+1
            clauses.extend(((z,a),(-z,-a)))
        else:
            a,b = args[0]+1,args[1]+1
            if op == 'and': clauses.extend(((-z,a),(-z,b),(z,-a,-b)))
            elif op == 'or': clauses.extend(((z,-a),(z,-b),(-z,a,b)))
            else: raise ValueError(op)
    clauses.append((output+1,))
    return q + len(gates), tuple(clauses)

def clause_clique(clauses):
    vertices = [(i, lit) for i,c in enumerate(clauses) for lit in c]
    edges = {(i,j) for i in range(len(vertices)) for j in range(i+1,len(vertices))
             if vertices[i][0] != vertices[j][0]
             and vertices[i][1] != -vertices[j][1]}
    return vertices, edges, len(clauses)

def is_clique(vertices, edges):
    return all(tuple(sorted((i,j))) in edges for i,j in combinations(vertices,2))

def assignment_to_clique(clauses, assignment):
    vertices, edges, m = clause_clique(clauses)
    chosen = []
    for c in range(m):
        chosen.append(next(i for i,(j,l) in enumerate(vertices)
                           if j==c and lit_value(l,assignment)))
    assert is_clique(chosen,edges)
    return tuple(chosen)

def clique_to_assignment(n, clauses, chosen):
    vertices,edges,m=clause_clique(clauses)
    assert len(set(chosen))==m and is_clique(chosen,edges)
    result=[False]*n
    for i in chosen:
        lit=vertices[i][1]
        result[abs(lit)-1]=(lit>0)
    assert cnf_value(clauses,result)
    return tuple(result)

def subset_sum_from_3cnf(n,clauses):
    assert all(len(c)<=3 for c in clauses)
    m=len(clauses)
    powers=[8**i for i in range(n+m)]
    numbers=[]
    for i in range(n):
        for bit in (False,True):
            value=powers[i]
            for j,c in enumerate(clauses):
                occurrences=sum(abs(lit)==i+1 and ((lit>0)==bit) for lit in c)
                value+=occurrences*powers[n+j]
            numbers.append(value)
    for j in range(m):
        numbers.extend((powers[n+j],2*powers[n+j]))
    target=sum(powers[:n])+4*sum(powers[n:])
    return numbers,target

def assignment_to_subset(n,clauses,assignment):
    assert len(assignment)==n and cnf_value(clauses,assignment)
    result=[]
    for bit in assignment: result.extend((not bit,bool(bit)))
    for c in clauses:
        slack=4-sum(lit_value(lit,assignment) for lit in c)
        assert 1<=slack<=3
        result.extend((bool(slack&1),bool(slack&2)))
    numbers,target=subset_sum_from_3cnf(n,clauses)
    assert sum(a for a,b in zip(numbers,result) if b)==target
    return tuple(result)

def subset_to_assignment(n,clauses,subset):
    numbers,target=subset_sum_from_3cnf(n,clauses)
    assert len(numbers)==len(subset)
    assert sum(a for a,b in zip(numbers,subset) if b)==target
    assert all(subset[2*i] != subset[2*i+1] for i in range(n))
    result=tuple(subset[2*i+1] for i in range(n))
    assert cnf_value(clauses,result)
    assert assignment_to_subset(n,clauses,result)==tuple(subset)
    return result

def partition_from_subset(numbers,target):
    total=sum(numbers)
    if target>total: return [1]
    if total==0: return [1,1] if target==0 else [1]
    return list(numbers)+[2*total-target,total+target]

def subset_sums(numbers):
    # Counts indexed subsets, even when values coincide.
    counts=Counter({0:1})
    for x in numbers:
        other=Counter({s+x:c for s,c in counts.items()})
        counts.update(other)
    return counts

def literal_index(lit):
    return 2*(abs(lit)-1)+(0 if lit>0 else 1)

def two_sat(n,clauses):
    if any(len(c)==0 for c in clauses): return None
    assert all(len(c)<=2 for c in clauses)
    size=2*n
    reach=[[i==j for j in range(size)] for i in range(size)]
    for c in clauses:
        a,b=(c[0],c[-1])
        ai,bi=literal_index(a),literal_index(b)
        reach[ai^1][bi]=True
        reach[bi^1][ai]=True
    for k in range(size):
        for i in range(size):
            for j in range(size):
                reach[i][j]=reach[i][j] or (reach[i][k] and reach[k][j])
    if any(reach[2*i][2*i+1] and reach[2*i+1][2*i] for i in range(n)):
        return None
    representative=[min(j for j in range(size) if reach[i][j] and reach[j][i])
                    for i in range(size)]
    reps=sorted(set(representative))
    key={r:(size+1)*sum(reach[d][r] for d in reps)+r for r in reps}
    result=tuple(key[representative[2*i]]>key[representative[2*i+1]]
                 for i in range(n))
    assert cnf_value(clauses,result)
    return result

def horn_sat(n,clauses):
    for c in clauses: assert sum(l>0 for l in c)<=1
    value=[False]*n
    for _ in range(n):
        for c in clauses:
            heads=[l-1 for l in c if l>0]
            body=[-l-1 for l in c if l<0]
            if heads and all(value[i] for i in body): value[heads[0]]=True
    if not cnf_value(clauses,value): return None
    return tuple(value)

def cover_approx(n,edges):
    used=set()
    for u,v in sorted(edges):
        if u not in used and v not in used: used.update((u,v))
    return used

def bounded_cover(n,edges,k):
    if not edges: return set()
    if k==0: return None
    if k>=n: return set(range(n))
    u,v=min(edges)
    for chosen in (u,v):
        residual={e for e in edges if chosen not in e}
        cover=bounded_cover(n,residual,k-1)
        if cover is not None: return cover|{chosen}
    return None

def is_cover(cover,edges):
    return all(u in cover or v in cover for u,v in edges)

def sat_search(n,clauses,oracle):
    if not oracle(n,clauses): return None
    fixed=list(clauses)
    assignment=[]
    for i in range(n):
        bit=not oracle(n,fixed+[(-i-1,)])
        assignment.append(bit)
        fixed.append((i+1 if bit else -i-1,))
    assert cnf_value(clauses,assignment)
    return tuple(assignment)

def circuit_to_horn(q, gates, output, inputs):
    # Each node has true rail 2*i+1 and false rail 2*i+2 (signed literals).
    def rail(i, truth): return 2*i+(1 if truth else 2)
    clauses=[(rail(i,bool(b)),) for i,b in enumerate(inputs)]
    for idx,gate in enumerate(gates):
        z=q+idx
        op,*args=gate
        if op=='const': clauses.append((rail(z,bool(args[0])),))
        elif op=='not':
            a=args[0]
            clauses.extend(((-rail(a,False),rail(z,True)),
                            (-rail(a,True),rail(z,False))))
        elif op=='and':
            a,b=args
            clauses.extend(((-rail(a,True),-rail(b,True),rail(z,True)),
                            (-rail(a,False),rail(z,False)),
                            (-rail(b,False),rail(z,False))))
        elif op=='or':
            a,b=args
            clauses.extend(((-rail(a,True),rail(z,True)),
                            (-rail(b,True),rail(z,True)),
                            (-rail(a,False),-rail(b,False),rail(z,False))))
        else: raise ValueError(op)
    clauses.append((-rail(output,False),))
    return 2*(q+len(gates)),clauses

def run_checks():
    statistics={}
    # Complete enumeration of all two-gate circuits on two inputs.
    def gates_on(n):
        return [('const',False),('const',True)]+[('not',i) for i in range(n)]+[
            (op,i,j) for op in ('and','or') for i in range(n) for j in range(n)]
    circuit_count=0
    circuit_horn_count=0
    for g0 in gates_on(2):
        for g1 in gates_on(3):
            for output in range(4):
                gates=[g0,g1]
                v,cnf=tseitin(2,gates,output)
                actual=sat_models(v,cnf)
                expected=[]
                for a in assignments(2):
                    bit,full=evaluate_circuit(2,gates,output,a)
                    if bit: expected.append(full)
                    hv,hcnf=circuit_to_horn(2,gates,output,a)
                    hsolution=horn_sat(hv,hcnf)
                    assert (hsolution is not None)==bit
                    if hsolution is not None: assert cnf_value(hcnf,hsolution)
                    circuit_horn_count+=1
                assert set(actual)==set(expected)
                assert len(actual)==len(expected)
                circuit_count+=1
    statistics['two_gate_circuits_with_unique_extension']=circuit_count
    statistics['dual_rail_circuit_to_horn_instances']=circuit_horn_count

    # Repeated literals are intentionally permitted; variables may be unused.
    clause_pool=list(combinations_with_replacement((-2,-1,1,2),3))
    formulas=[c for m in range(3) for c in combinations_with_replacement(clause_pool,m)]
    formulas += [((),), ((1,),), ((1,-1),), ((),(1,)), ((1,1,1),(-1,-1,-1))]
    subset_witness_count=0
    clique_witness_count=0
    for clauses in formulas:
        models=sat_models(2,clauses)
        numbers,target=subset_sum_from_3cnf(2,clauses)
        solutions=[bits for bits in assignments(len(numbers))
                   if sum(x for x,b in zip(numbers,bits) if b)==target]
        assert len(solutions)==len(models)
        assert set(solutions)=={assignment_to_subset(2,clauses,a) for a in models}
        for s in solutions:
            assert subset_to_assignment(2,clauses,s) in models
        subset_witness_count+=len(solutions)
        vertices,edges,m=clause_clique(clauses)
        cliques=[c for c in combinations(range(len(vertices)),m) if is_clique(c,edges)]
        assert bool(cliques)==bool(models)
        for a in models: assignment_to_clique(clauses,a)
        for c in cliques: clique_to_assignment(2,clauses,c)
        clique_witness_count+=len(cliques)
    statistics['cnf_graph_and_subset_sum_instances']=len(formulas)
    statistics['subset_sum_witness_bijections_checked']=subset_witness_count
    statistics['clique_reverse_witnesses_checked']=clique_witness_count

    partition_count=0
    for length in range(5):
        for numbers in product(range(4),repeat=length):
            sums=subset_sums(numbers)
            for target in range(sum(numbers)+2):
                yes=target in sums
                part=partition_from_subset(numbers,target)
                total=sum(part)
                part_yes=(total%2==0 and total//2 in subset_sums(part))
                assert yes==part_yes
                knap_yes=any(s<=target and s>=target for s in sums)
                assert yes==knap_yes
                partition_count+=1
    statistics['subset_sum_partition_knapsack_instances']=partition_count

    # All sets of binary clauses on two variables, including repeated literals
    # (which encode unit clauses); compare with the independent truth table.
    binary=list(combinations_with_replacement((-2,-1,1,2),2))
    two_sat_count=0
    for choose in assignments(len(binary)):
        clauses=[c for c,b in zip(binary,choose) if b]
        models=sat_models(2,clauses)
        solution=two_sat(2,clauses)
        assert (solution is not None)==bool(models)
        if solution is not None: assert solution in models
        two_sat_count+=1
    assert two_sat(0,[])==()
    assert two_sat(0,[()]) is None
    rng=Random(20261122)
    for _ in range(300):
        clauses=[tuple(rng.choice((-3,-2,-1,1,2,3)) for _ in range(rng.randrange(3)))
                 for _ in range(rng.randrange(12))]
        solution=two_sat(3,clauses)
        assert (solution is not None)==bool(sat_models(3,clauses))
        two_sat_count+=1
    statistics['two_sat_differential_instances']=two_sat_count+2

    # All Horn clause sets over two variables, with no repeated literal needed.
    all_literals=(-2,-1,1,2)
    horn_clauses=[c for length in range(4) for c in combinations(all_literals,length)
                  if sum(l>0 for l in c)<=1]
    horn_count=0
    for choose in assignments(len(horn_clauses)):
        clauses=[c for c,b in zip(horn_clauses,choose) if b]
        models=sat_models(2,clauses)
        solution=horn_sat(2,clauses)
        assert (solution is not None)==bool(models)
        if solution is not None:
            assert solution in models
            assert all(all(not b or a for b,a in zip(solution,model)) for model in models)
        horn_count+=1
    statistics['horn_sat_least_model_instances']=horn_count

    graph_count=0
    parameter_count=0
    for n in range(6):
        possible=list(combinations(range(n),2))
        for edge_bits in assignments(len(possible)):
            edges={e for e,b in zip(possible,edge_bits) if b}
            covers=[{i for i,b in enumerate(bits) if b} for bits in assignments(n)
                    if is_cover({i for i,b in enumerate(bits) if b},edges)]
            optimum=min(map(len,covers))
            approx=cover_approx(n,edges)
            assert is_cover(approx,edges) and len(approx)<=2*optimum
            for k in range(n+1):
                solution=bounded_cover(n,edges,k)
                assert (solution is not None)==(optimum<=k)
                if solution is not None: assert is_cover(solution,edges) and len(solution)<=k
                parameter_count+=1
            graph_count+=1
    statistics['all_graphs_through_five_vertices_approximation']=graph_count
    statistics['parameterized_vertex_cover_instances']=parameter_count

    search_count=0
    oracle=lambda n,c:bool(sat_models(n,c))
    for clauses in formulas:
        answer=sat_search(2,list(clauses),oracle)
        assert (answer is not None)==bool(sat_models(2,clauses))
        if answer is not None: assert cnf_value(clauses,answer)
        search_count+=1
    statistics['sat_search_oracle_instances']=search_count
    statistics['status']='PASS'
    return statistics

if __name__=='__main__':
    print(json.dumps(run_checks(),indent=2,sort_keys=True))
