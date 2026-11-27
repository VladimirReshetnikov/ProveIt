#!/usr/bin/env python3
"""Exact finite checks for p-primary Euler-factor disagreement theorems.
No floating point. Uses full value histograms, not traces.
"""
from collections import Counter
from itertools import product, combinations_with_replacement
from math import prod, lcm, gcd
import argparse, json
from pathlib import Path


def group(moduli):
    return list(product(*(range(n) for n in moduli)))


def add(x,y,moduli):
    return tuple((a+b)%n for a,b,n in zip(x,y,moduli))


def sub(x,y,moduli):
    return tuple((a-b)%n for a,b,n in zip(x,y,moduli))


def subgroup(generators,moduli):
    zero=(0,)*len(moduli)
    h={zero}
    for g in generators:
        prev=list(h)
        t=g
        while t!=zero:
            h.update(add(x,t,moduli) for x in prev)
            t=add(t,g,moduli)
    return h


def is_coset_equality(c,elements,moduli,p):
    pos=[elements[i] for i,v in enumerate(c) if v>0]
    neg=[elements[i] for i,v in enumerate(c) if v<0]
    if not pos or max(map(abs,c))!=1:
        return False
    a,b=pos[0],neg[0]
    h=subgroup([sub(x,a,moduli) for x in pos]+[sub(y,b,moduli) for y in neg],moduli)
    if set(pos)!={add(a,h0,moduli) for h0 in h} or set(neg)!={add(b,h0,moduli) for h0 in h}:
        return False
    delta=sub(b,a,moduli)
    return any(all((p*t)%n==0 for t,n in zip(sub(delta,h0,moduli),moduli)) for h0 in h)


def is_saturated_equality(c,el,moduli,p,ev,support):
    n=len(el); e=lcm(*moduli); b=min(moduli)
    for vi in support:
        v=el[vi]
        if all(t%p==0 for t in v):
            continue
        order=lcm(*(ni//gcd(ni,ti) for ni,ti in zip(moduli,v)))
        if order!=b:
            continue
        orbit={tuple((u*ti)%ni for ti,ni in zip(v,moduli)) for u in range(order) if u%p}
        if {el[j] for j in support}!=orbit:
            continue
        gs={}
        for x,value in enumerate(c):
            label=ev[vi][x]//(e//b)
            if label in gs and gs[label]!=value:
                break
            gs[label]=value
        else:
            if all(sum(gs[u+j*(b//p)] for j in range(p))==0 for u in range(b//p)):
                return True
    return False


def check_case(moduli,p,k):
    el=group(moduli); n=len(el); e=lcm(*moduli); b=min(moduli)
    ev=[[sum(xi*vi*(e//ni) for xi,vi,ni in zip(x,v,moduli))%e for x in el] for v in el]
    packets=list(combinations_with_replacement(range(n),k))
    sig=[tuple(tuple(sorted(row[x] for x in a)) for row in ev) for a in packets]
    counts=[Counter(a) for a in packets]
    pairs=0; eq=0; saturated=0; minimum=n; minpair=None
    for i,a in enumerate(packets):
        ca=counts[i]
        for j in range(i):
            size=sum(u!=v for u,v in zip(sig[i],sig[j]))
            cb=counts[j]
            common=sum(min(amt,cb.get(x,0)) for x,amt in ca.items())
            m=k-common
            assert size*p*m >= (p-1)*n
            assert size >= b-b//p
            if size<minimum:
                minimum=size; minpair=(a,packets[j])
            c=[ca.get(x,0)-cb.get(x,0) for x in range(n)]
            assert size*p*m >= (p-1)*n*max(map(abs,c))
            if size*p*m==(p-1)*n:
                assert is_coset_equality(c,el,moduli,p)
                eq+=1
            if size==b-b//p:
                support=[vi for vi,(u,v) in enumerate(zip(sig[i],sig[j])) if u!=v]
                assert is_saturated_equality(c,el,moduli,p,ev,support)
                saturated+=1
            pairs+=1
    return {'moduli':moduli,'p':p,'packet_size':k,'packets':len(packets),'pairs':pairs,'minimum_numerator':minimum,'density_denominator':n,'sharp_bound_pairs':eq,'saturated_pairs':saturated,'minimum_example':minpair}


def construction_checks():
    cases=[((4,4),2),((8,4),2),((9,3),3),((9,9),3),((4,2,2),2),((8,8),2),((25,5),5)]
    result=[]
    for raw,p in cases:
        moduli=tuple(sorted(raw)); el=group(moduli); n=len(el); e=lcm(*moduli); M=n//moduli[0]
        t=(moduli[0]//p,)+(0,)*(len(moduli)-1)
        k=1
        while k<=M:
            todo=k; generators=[]
            for i,ni in enumerate(moduli[1:],start=1):
                take=1
                while todo%p==0 and take<ni:
                    todo//=p;take*=p
                g=[0]*len(moduli);g[i]=ni//take
                if take>1: generators.append(tuple(g))
            assert todo==1
            P=subgroup(generators,moduli)
            assert len(P)==k and t not in P
            A=P;B={add(x,t,moduli) for x in P}
            supp=[]
            for v in el:
                vals=lambda T:sorted(sum(xi*vi*(e//ni) for xi,vi,ni in zip(x,v,moduli))%e for x in T)
                if vals(A)!=vals(B):supp.append(v)
            assert len(supp)*p*k==(p-1)*n
            result.append({'moduli':moduli,'packet_size':k,'disagreement_count':len(supp),'group_size':n})
            k*=p
    # Actual quartic Dirichlet example modulo 65.
    log5={pow(2,j,5):j for j in range(4)}
    log13={pow(2,j,13):j for j in range(12)}
    residues=[r for r in range(65) if gcd(r,65)==1]
    disagree=[]
    for r in residues:
        a=log5[r%5]%4
        beta=log13[r%13]%4
        A=sorted((j*a)%4 for j in range(4))
        B=sorted((2*beta+j*a)%4 for j in range(4))
        if A!=B:disagree.append(r)
    assert len(residues)==48 and len(disagree)==6
    assert all(log5[r%5]==0 and log13[r%13]%2 for r in disagree)
    # Quotient order p alone is insufficient: C4 / {0,2}.
    false_lift=[v for v in range(4) if sorted((v*x)%4 for x in (0,2)) != sorted((v*x)%4 for x in (1,3))]
    assert false_lift==[1,2,3]
    return result,{'modulus':65,'unit_count':48,'disagreement_residues':disagree,'density':'1/8'}, {'group_moduli':[4],'positive_coset':[0,2],'negative_coset':[1,3],'disagreement_evaluations':false_lift,'density':'3/4'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'output')
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    lines=[]
    cases=[((4,),2,2),((8,),2,3),((9,),3,3),((4,2),2,3),((4,4),2,2),((4,4),2,3),((4,4),2,4),((3,3),3,3),((9,3),3,2)]
    results=[]
    for case in cases:
        r=check_case(*case);results.append(r);line=json.dumps(r);lines.append(line);print(line,flush=True)
    constructions,quartic,false_lift=construction_checks()
    line=json.dumps({'construction_count':len(constructions),'quartic_example':quartic,'torsion_lift_counterexample':false_lift});lines.append(line);print(line,flush=True)
    payload={'cases':results,'total_pairs':sum(r['pairs'] for r in results),'constructions':constructions,'quartic_example':quartic,'torsion_lift_counterexample':false_lift}
    (args.output_dir/'pprimary_verification.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
    (args.output_dir/'pprimary_verification.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')

if __name__=='__main__': main()
