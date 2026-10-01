#!/usr/bin/env python3
"""Reproducible exact finite checks; these supplement, not replace, the proofs."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from diophantine_compiler import (PetriNet, app, unapp, ski_step, monitor,
    compile_petri,compile_fractran,compile_ski,fractran_run,mutation_audit)


def normal_form_exhaustive() -> dict:
    words_checked=classes_checked=graphs=0
    for r in range(1,5):
        pairs=list(itertools.combinations(range(r),2))
        for mask in range(1<<len(pairs)):
            I=set()
            for i,(a,b) in enumerate(pairs):
                if (mask>>i)&1:
                    I.update(((a,b),(b,a)))
            graphs+=1
            for T in range(6):
                words=list(itertools.product(range(r),repeat=T))
                parent={w:w for w in words}
                def find(w):
                    while parent[w]!=w:
                        parent[w]=parent[parent[w]]
                        w=parent[w]
                    return w
                for w in words:
                    for k in range(T-1):
                        if (w[k],w[k+1]) in I:
                            v=w[:k]+(w[k+1],w[k])+w[k+2:]
                            a,b=find(w),find(v)
                            if a!=b:
                                parent[max(a,b)]=min(a,b)
                minima={}
                for w in words:
                    root=find(w)
                    minima[root]=min(minima.get(root,w),w)
                for w in words:
                    good,_=monitor(w,r,I)
                    assert good==(w==minima[find(w)]),(r,I,w)
                words_checked+=len(words)
                classes_checked+=len(minima)
    return dict(graphs=graphs,words=words_checked,classes=classes_checked,max_length=5)


def monitor_lower_bound() -> dict:
    checked=0
    for k in range(1,8):
        r=2*k+1
        b=2*k
        I=set()
        for i in range(k):
            I.update(((b,k+i),(k+i,b)))
            for j in range(k):
                if i!=j:
                    I.update(((i,k+j),(k+j,i)))
        states=set()
        for mask in range(1<<k):
            prefix=(b,)+tuple(i for i in range(k) if (mask>>i)&1)
            good,rows=monitor(prefix,r,I)
            assert good
            state=tuple(rows[-1][k:2*k]);states.add(state)
            for i in range(k):
                good,_=monitor(prefix+(k+i,),r,I)
                assert good==bool((mask>>i)&1)
            checked+=1
        assert len(states)==1<<k
    return dict(max_k=7,prefixes=checked)


def petri_checks() -> dict:
    random.seed(94173)
    net_count=word_count=certificate_count=0
    for trial in range(24):
        p=r=3
        pre=[];post=[]
        for a in range(r):
            # sparse footprints include independent transitions in most examples
            support=random.sample(range(p),random.randint(1,2))
            pre.append(tuple(random.randint(0,1) if j in support else 0 for j in range(p)))
            post.append(tuple(random.randint(0,1) if j in support else 0 for j in range(p)))
        net=PetriNet(tuple(pre),tuple(post))
        start=tuple(random.randint(0,2) for _ in range(p))
        I=net.independence();net_count+=1
        for T in range(5):
            for word in itertools.product(range(r),repeat=T):
                word_count+=1
                rows=net.run(start,word)
                if rows is None:
                    continue
                good,_=monitor(word,r,I)
                s=compile_petri(net,start,rows[-1],T,word)
                assert (s.energy()==0)==good
                assert len(s.variables)==(p+r)*(2*T+1)
                assert len(s.residuals)==2*p+r+T*(2*r+2*p+2)
                assert max(q.degree for _,q in s.residuals)<=2
                for j in range(T-1):
                    if (word[j],word[j+1]) in I:
                        swapped=word[:j]+(word[j+1],word[j])+word[j+2:]
                        other=net.run(start,swapped)
                        assert other is not None and other[-1]==rows[-1]
                certificate_count+=1
    net=PetriNet(((0,),),((1,),))
    s=compile_petri(net,(0,),(1,),1)
    roots=[]
    for vector in itertools.product(range(3),repeat=len(s.variables)):
        if s.energy(dict(zip(s.variables,vector)))==0:
            roots.append(vector)
    assert len(roots)==1
    return dict(nets=net_count,words=word_count,evaluated_certificates=certificate_count,
                exhaustive_small_domain_assignments=3**len(s.variables),small_domain_roots=len(roots))


def fractran_checks() -> dict:
    from math import gcd
    fractions=[(a,b) for a in range(1,5) for b in range(1,5) if gcd(a,b)==1]
    programs=[(f,) for f in fractions]+list(itertools.product(fractions,repeat=2))
    certificates=0
    for program in programs:
        for start in range(1,13):
            for T in range(4):
                rows=fractran_run(program,start,T)
                if rows is None:
                    continue
                s=compile_fractran(program,start,rows[-1],T)
                assert s.energy()==0
                r=len(program)
                assert len(s.variables)==T*(7*r+2)+1
                assert len(s.residuals)==2+T*(8*r+3)
                assert all(p.degree<=2 for _,p in s.residuals)
                certificates+=1
    # Includes reduction of a non-reduced fraction and a denominator-one branch.
    for program in (((6,4),(1,1)),((3,1),(1,2))):
        rows=fractran_run(program,8,4)
        assert compile_fractran(program,8,rows[-1],4).energy()==0
    return dict(programs=len(programs),inputs_per_program=12,max_horizon=3,
                certificates=certificates+2)


def ski_checks() -> dict:
    for n in range(3,2000):
        l,r=unapp(n)
        assert app(l,r)==n and l<n and r<n
    checked=0
    for x,y,z in itertools.product(range(5),repeat=3):
        for rule,source in (('I',app(2,x)),('K',app(app(1,x),y)),
                            ('S',app(app(app(0,x),y),z))):
            for path in ('','L','R','LR','RL'):
                code=source
                # Construct an outer context whose selected hole has path.
                for d in reversed(path):
                    code=app(code,1) if d=='L' else app(1,code)
                finish=ski_step(code,rule,path)
                s=compile_ski(code,finish,[(rule,path)])
                assert s.energy()==0
                k={'I':1,'K':3,'S':7}[rule];e={'I':2,'K':3,'S':6}[rule]
                assert len(s.variables)==2+3*len(path)+k
                assert len(s.residuals)==2+2*len(path)+e
                assert all(p.degree<=2 for _,p in s.residuals)
                checked+=1
    return dict(codes_inverted=1997,certificates=checked)


def examples() -> dict:
    out=ROOT/'examples';out.mkdir(exist_ok=True)
    net=PetriNet(((1,0,0,0,0),(0,0,1,0,0),(0,1,0,1,0)),
                 ((0,1,0,0,0),(0,0,0,1,0),(0,0,0,0,1)))
    start=(1,0,1,0,0);finish=(0,0,0,0,1)
    petri=compile_petri(net,start,finish,3,(0,1,2))
    petri.dump(str(out/'petri_fork_join.json'))
    nonnormal=compile_petri(net,start,finish,3,(1,0,2))
    assert nonnormal.energy()>0
    fractran=compile_fractran(((3,2),(5,3)),8,125,6,terminal=True)
    fractran.dump(str(out/'fractran_first_halt.json'))
    source=app(app(app(0,1),2),2)
    ski=compile_ski(source,2,[('S',''),('K','')])
    ski.dump(str(out/'ski_SKII.json'))
    contextual_source=app(2,app(2,1))
    ctx=compile_ski(contextual_source,1,[('I','R'),('I','')])
    ctx.dump(str(out/'ski_context.json'))
    systems={'petri_fork_join':petri,'fractran_first_halt':fractran,
             'ski_SKII':ski,'ski_context':ctx}
    results={}
    for name,s in systems.items():
        results[name]={'variables':len(s.variables),'equations':len(s.residuals),
                       'maximum_witness':max(s.witness.values(),default=0),
                       'energy':s.energy(),'rejected_one_coordinate_mutations':mutation_audit(s)}
    results['fractran_sequence']=fractran_run(((3,2),(5,3)),8,6)
    results['ski_source_code']=source
    results['context_source_code']=contextual_source
    return results

if __name__=='__main__':
    began=time.monotonic()
    report={}
    for name,fun in [('normal_forms',normal_form_exhaustive),('memory_lower_bound',monitor_lower_bound),
                     ('petri',petri_checks),('fractran',fractran_checks),('ski',ski_checks),
                     ('examples',examples)]:
        report[name]=fun()
        print(name,json.dumps(report[name]),flush=True)
    report['status']='PASS'
    report['elapsed_seconds']=round(time.monotonic()-began,3)
    (ROOT/'tests'/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('ALL TESTS PASSED',report['elapsed_seconds'],flush=True)
