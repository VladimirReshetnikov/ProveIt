#!/usr/bin/env python3
"""Independent exact checks of the new size-three physical-cover assembly.
No producer code imported.  These tests corroborate the ordinary assembly proof;
the previously audited boundary theorem is a separate, explicit premise.
"""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib, json, random, time

OUT=Path(__file__).resolve().parent
C=7

def supports(arcs):
    ans={(0,0)}
    for a,b in arcs:
        mask=(1<<a)|(1<<b)
        for S,T in tuple(ans):
            if not ((S|T)&mask): ans.add((S|(1<<a),T|(1<<b)))
    return ans

def mono(pair,n):
    S,T=pair
    return tuple((S>>v)&1 for v in range(n))+tuple((T>>v)&1 for v in range(n))

def add(a,b):return tuple(x+y for x,y in zip(a,b))

def poly_product(A,B):
    ans=Counter()
    for a in A:
        for b in B:ans[add(a,b)]+=1
    return ans

def classes(arcs,n):
    fam=supports(arcs)
    pol={'H':set(),'c':set()}
    pol.update({('a',i):set() for i in range(3)})
    pol.update({('b',i,j):set() for i,j in combinations(range(3),2)})
    for p in fam:
        S,T=p; k=S.bit_count(); core=(S|T)&C; mon=mono(p,n)
        if k==1 and core.bit_count()==1:pol['a',core.bit_length()-1].add(mon)
        if k==2 and core.bit_count()==2:
            i,j=[v for v in range(3) if core>>v&1];pol['b',i,j].add(mon)
        if k==2 and core==C:pol['H'].add(mon)
        if k==3:pol['c'].add(mon)
    return pol,fam

def internal_witness_check():
    # The one-exterior localization is complete for H and the w_ij.
    n=4; possible=list(permutations(range(n),2)); hist=Counter(); count=0
    for bits in range(1<<len(possible)):
        arcs=[e for h,e in enumerate(possible) if bits>>h&1]
        pol,fam=classes(arcs,n); ws=[]
        for i,j in combinations(range(3),2):
            k=3-i-j
            E={mono((1<<a,1<<b),n) for a,b in arcs if {a,b}=={i,j}}
            w=poly_product(E,pol['a',k]);ws.append(w)
            assert all(coef==1 and mon in pol['H'] for mon,coef in w.items())
        total=sum(ws,Counter())
        assert set(total)==pol['H']
        assert all(coef in (1,2) for coef in total.values())
        for mon in pol['H']:hist[total[mon]]+=1
        count+=len(fam)
    return {'graph_cases':1<<len(possible),'support_instances':count,'H_witness_multiplicity_histogram':dict(hist)}

def removal_check():
    # Each c monomial has three distinct exterior vertices, all roles fixed.
    # Strip every role-incompatible arc; this leaves 20 types and 1,600 graphs.
    n=6; hist=Counter(); graphcases=0;positive=0
    for tails in combinations(range(n),3):
        S=sum(1<<v for v in tails);T=((1<<n)-1)^S; target=mono((S,T),n)
        possible=[(a,b) for a in tails for b in range(n) if T>>b&1 and (a<3)!=(b<3)]
        for bits in range(1<<len(possible)):
            arcs=[e for h,e in enumerate(possible) if bits>>h&1];pol,fam=classes(arcs,n)
            c=int((S,T) in fam);positive+=c;graphcases+=1
            for k in range(3):
                i,j=[v for v in range(3) if v!=k]
                coef=poly_product(pol['a',k],pol['b',i,j])[target]
                assert coef>=c
                hist[coef-c]+=1
    return {'role_types':20,'graph_cases':graphcases,'positive_c_targets':positive,'checked_inequality_instances':sum(hist.values()),'gap_histogram':dict(hist)}

def weight(mon,acts):
    ans=1
    for x,e in zip(acts,mon):
        if e:ans*=x**e
    return ans

def numerical_assembly_check():
    rng=random.Random(20261001); graphs=0;evals=0; degrees=Counter();max_multiplicity=0
    # Exact integer evaluations, including zeros and opposite arcs.
    for m in range(7):
        n=3+m
        possible=[(a,b) for a,b in permutations(range(n),2) if a<3 or b<3]
        for case in range(120):
            cutoff=0 if case==0 else 1 if case==1 else rng.random()
            arcs=[e for e in possible if rng.random()<cutoff]
            pol,fam=classes(arcs,n);graphs+=1
            for trial in range(12):
                acts=[rng.randrange(5) if trial<10 else 1 for _ in range(2*n)]
                if trial==11:acts[rng.randrange(2*n)]=0
                G=[0]*4
                for pair in fam:G[pair[0].bit_count()]+=weight(mono(pair,n),acts)
                d=max(k for k,v in enumerate(G) if v);degrees[d]+=1
                A=sum(sum(weight(mon,acts) for mon in pol['a',i]) for i in range(3))
                bs=[sum(weight(mon,acts) for mon in pol['b',i,j]) for i,j in combinations(range(3),2)]
                H=sum(weight(mon,acts) for mon in pol['H']);c=sum(weight(mon,acts) for mon in pol['c'])
                E=sum(acts[a]*acts[n+b] for a,b in arcs if a<3 and b<3)
                assert G==[1,A+E,sum(bs)+H,c]
                ws=[]
                for i,j in combinations(range(3),2):
                    k=3-i-j
                    ep=sum(acts[a]*acts[n+b] for a,b in arcs if {a,b}=={i,j})
                    ak=sum(weight(mon,acts) for mon in pol['a',k])
                    ws.append(ep*ak)
                assert max(ws,default=0)<=H and sum(ws)<=2*H
                assert E*c<=sum(w*b for w,b in zip(ws,bs))
                x,y,z=sorted(bs,reverse=True)
                assert E*c<=H*(x+y)
                assert A*c<=x*y+x*z+y*z
                gap=G[2]**2-3*G[1]*G[3]
                assert 4*gap >= (2*z+2*H-x-y)**2+3*(x-y)**2
                # Actual-degree first Newton inequality is valid for all d>=2.
                if d>=2:assert (d-1)*G[1]**2>=2*d*G[2]
                if d==3:assert G[2]**2>=3*G[1]*G[3]
                evals+=1
    return {'graph_cases':graphs,'integer_activity_evaluations':evals,'actual_degree_histogram':dict(degrees),'maximum_exterior_size':6,'role_activity_values':[0,1,2,3,4],'note':'Corroborative bounded tests only; the ordinary proof and approved boundary premise establish all-size scope.'}

def main():
    start=time.monotonic()
    result={'verdict':'PASS','internal_witness_checks':internal_witness_check(),'forced_core_removal_checks':removal_check(),'integer_assembly_checks':numerical_assembly_check(),'elapsed_seconds':round(time.monotonic()-start,3)}
    result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (OUT/'independent_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
