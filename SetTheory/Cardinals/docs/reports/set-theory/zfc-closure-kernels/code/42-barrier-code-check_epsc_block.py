#!/usr/bin/env python3
"""Independent finite check of the six shared-witness EPSC clause templates.

This reads the emitted JSON, not its generator.  E and the represented R are
arbitrary finite relations.  This tests only the EPSC clause transformation;
it does not assert a finite model of the whole assignment/class theory.
"""
from __future__ import annotations
import argparse
import copy
import itertools
import json
from pathlib import Path

NAMES = ('unbounded_output', 'unbounded_member', 'unbounded_escape',
         'empty_closure', 'member_closure', 'support')

def rel(mask, n):
    return tuple(tuple(bool(mask & (1 << (i*n+j))) for j in range(n)) for i in range(n))

def original(E, R, n):
    subsets = [[all(not E[z][y] or E[z][d] for z in range(n))
                for d in range(n)] for y in range(n)]
    bad = [x for x in range(n) if not any(
        all(not R[x][y] or subsets[y][d] for y in range(n)) for d in range(n))]
    empty = [not any(E[z][x] for z in range(n)) for x in range(n)]
    hulls = [h for h in range(n)
             if all(not ((empty[x] or E[x][h]) and R[x][y]) or E[y][h]
                    for x in range(n) for y in range(n))
             and all(not E[y][h] or any(R[x][y] for x in range(n)) for y in range(n))]
    return bool(bad or hulls), bad, hulls

def variables(term):
    if isinstance(term, str): return {term}
    return set().union(*(variables(x) for x in term[1:]))

def prepare(payload, n):
    clauses = {c['name']:c for c in payload['clauses']}
    out=[]
    for name in NAMES:
        c=clauses[name]
        vs=sorted(set().union(*(variables(t) for l in c['literals'] for t in l['args']))-{'?b','?t'})
        envs=[dict(zip(vs,vals), **{'?b':'BASE','?t':'CODE'})
              for vals in itertools.product(range(n),repeat=len(vs))]
        out.append((c,envs))
    return out

def clause_model(prepared, E, R, g, k, u, w):
    def term(t,env):
        if isinstance(t,str): return env[t]
        name=t[0]
        a=[term(q,env) for q in t[1:]]
        if name=='o': return 0
        if name=='q': return 1
        if name=='N':
            assert a==[0,0]
            return 1
        if name=='G':
            assert a==['BASE','CODE']
            return g
        if name=='K':
            assert a==['BASE','CODE']
            return k
        if name in ('U','T'):
            assert a[:2]==['BASE','CODE']
            return (u if name=='U' else w)[a[2]]
        if name=='C':
            if a[0]=='BASE':
                assert a[1]==0
                return ('x',a[2])
            assert a[0][0]=='x' and a[1]==1
            return ('xy',a[0][1],a[2])
        raise AssertionError(('unexpected_function',name))
    def literal(l,env):
        a=[term(t,env) for t in l['args']]
        if l['predicate']=='eq': value=a[0]==a[1]
        elif l['predicate']=='B':
            assert a==['BASE','CODE']
            value=(g==0)
        elif l['predicate']=='E': value=E[a[0]][a[1]]
        elif l['predicate']=='P':
            assert a[1]=='CODE' and a[0][0]=='xy'
            value=R[a[0][1]][a[0][2]]
        else: raise AssertionError(l['predicate'])
        return value == l['positive']
    return all(any(literal(l,env) for l in c['literals']) for c,envs in prepared for env in envs)

def choose(E,R,n,bad,hulls):
    if bad:
        k=bad[0];u=[];w=[]
        for d in range(n):
            y,z=next((y,z) for y in range(n) for z in range(n)
                     if R[k][y] and E[z][y] and not E[z][d])
            u.append(y);w.append(z)
        return 0,k,u,w
    k=hulls[0]
    u=[next((x for x in range(n) if R[x][y]),0) for y in range(n)]
    w=[next((z for z in range(n) if E[z][x]),0) for x in range(n)]
    return 1,k,u,w

def exhaustive_two(payload):
    n=2;prepared=prepare(payload,n);total=valid=positive=0
    witnesses=list(itertools.product(range(2),range(n),itertools.product(range(n),repeat=n),itertools.product(range(n),repeat=n)))
    for em in range(1<<(n*n)):
        E=rel(em,n)
        for rm in range(1<<(n*n)):
            R=rel(rm,n);expected,_,_=original(E,R,n);found=False
            for g,k,u,w in witnesses:
                total+=1
                ok=clause_model(prepared,E,R,g,k,u,w)
                if ok:
                    valid+=1;found=True
                    assert expected,('unsound',em,rm,g,k,u,w)
            assert found==expected,('incomplete',em,rm)
            positive+=expected
    return {'relation_pairs':256,'shared_function_assignments':total,'satisfying_assignments':valid,'satisfiable_instances':positive}

def constructed_three(payload):
    n=3;prepared=prepare(payload,n);checked=bad_cases=hull_cases=negative=0
    for em in range(1<<(n*n)):
        E=rel(em,n)
        for rm in range(1<<(n*n)):
            R=rel(rm,n);expected,bad,hulls=original(E,R,n)
            if not expected:
                negative+=1;continue
            assignment=choose(E,R,n,bad,hulls)
            assert clause_model(prepared,E,R,*assignment),('witness_failed',em,rm,assignment)
            checked+=1
            bad_cases+=bool(bad);hull_cases+=not bool(bad)
    return {'relation_pairs':262144,'constructed_expansions':checked,'unbounded_branch':bad_cases,'hull_branch':hull_cases,'false_original_instances':negative}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('payload',type=Path)
    ap.add_argument('--three',action='store_true');ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();payload=json.loads(args.payload.read_text())
    result={'scope':__doc__,'two':exhaustive_two(payload)}
    print(json.dumps(result['two']),flush=True)
    if args.three:
        result['three']=constructed_three(payload)
        print(json.dumps(result['three']),flush=True)
    # Guard-polarity and support-sign mutations are concrete correctness risks.
    mutations=[]
    for name,index in [('unbounded_output',0),('empty_closure',0),('support',2)]:
        mutated=copy.deepcopy(payload)
        c=next(c for c in mutated['clauses'] if c['name']==name)
        c['literals'][index]['positive']=not c['literals'][index]['positive']
        try:
            exhaustive_two(mutated)
        except AssertionError as exc:
            mutations.append({'clause':name,'literal':index,'rejected':True,'witness':str(exc)})
        else: raise AssertionError(('mutation_not_detected',name,index))
    result['mutations']=mutations
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'mutation_rejections':len(mutations)}))

if __name__=='__main__': main()
