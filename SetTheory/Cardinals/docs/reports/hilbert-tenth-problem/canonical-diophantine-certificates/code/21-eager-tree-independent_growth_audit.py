#!/usr/bin/env python3
"""Independent finite verification for exact fixed-R call count.
Does not import experimental evaluator, generator or other growth verifiers.
"""
import json, hashlib
from pathlib import Path
from functools import lru_cache
from fractions import Fraction
P = Path(__file__).with_name('shared_symbolic_proofs.json')
data=json.loads(P.read_text()); nodes=data['nodes']
cases={c['name']:c['rows'] for c in data['cases']}

@lru_cache(None)
def depends(i):
    return nodes[i][0]=='X' or any(depends(a) for a in nodes[i][1:])

@lru_cache(None)
def strip(i):
    s=0
    while nodes[i][0]=='S':
        s+=1;i=nodes[i][1]
    return s,i

@lru_cache(None)
def equations(i,j):
    """Conditions for T_i(v_k)=T_j(v_l), represented a*k+b*l=c.
    None means structurally impossible. Constants are fully DAG-compared.
    """
    s,i=strip(i);t,j=strip(j)
    A,B=nodes[i],nodes[j]
    if A[0]=='F' or B[0]=='F':
        if A[0]!='F' or B[0]!='F' or s!=t:return None
        e=equations(A[1],B[1]); f=equations(A[2],B[2])
        return None if e is None or f is None else e|f
    assert A[0] in ('L','X') and B[0] in ('L','X')
    return frozenset([(int(A[0]=='X'),-int(B[0]=='X'),t-s)])

def solve(es):
    if es is None:return None
    es=sorted(es)
    if any(a==b==0 and c for a,b,c in es):return None
    es=[e for e in es if e[0] or e[1]]
    if not es:return ('all',)
    a,b,c=es[0]
    for d,e,f in es[1:]:
        det=a*e-b*d
        if det:
            k=Fraction(c*e-b*f,det);l=Fraction(a*f-c*d,det)
            if any(u*k+v*l!=w for u,v,w in es):return None
            if k.denominator!=1 or l.denominator!=1 or k<0 or l<0:return None
            return ('point',int(k),int(l))
        if a*f!=d*c or b*f!=e*c:return None
    if b==0:
        k=Fraction(c,a)
        return ('k',int(k)) if k.denominator==1 and k>=0 else None
    if a==0:
        l=Fraction(c,b)
        return ('l',int(l)) if l.denominator==1 and l>=0 else None
    assert a==-b
    return ('shift',int(Fraction(c,a))) # k-l = c/a

def pair_eq(r,s):
    e=equations(r['x'],s['x']);f=equations(r['y'],s['y'])
    return solve(None if e is None or f is None else e|f)

reach={}
for name,rows in cases.items():
    seen={0};todo=[0]
    while todo:
        for i in rows[todo.pop()]['premises']:
            if i not in seen:seen.add(i);todo.append(i)
    assert len(seen)==len(rows)
    reach[name]={'total':len(rows),'reachable':len(seen),'reachable_oracles':[i for i in seen if rows[i]['oracle']]}

# Both ground bases have distinct canonical call keys.
for name in ('base0','base1'):
    rows=cases[name]
    assert all(not depends(r['x']) and not depends(r['y']) for r in rows)
    assert not [(i,j) for i in range(len(rows)) for j in range(i) if pair_eq(rows[i],rows[j])]

base=cases['base1'];step=cases['step']; nonoracle=[i for i,r in enumerate(step) if not r['oracle']]
ground=[i for i in nonoracle if not depends(step[i]['x']) and not depends(step[i]['y'])]
variable=[i for i in nonoracle if i not in ground]
assert len(base)==179 and len(ground)==80 and len(variable)==69
# No duplicate base calls.
assert not [(i,j) for i in range(len(base)) for j in range(i) if pair_eq(base[i],base[j])]
# All fixed step calls are already in base1.
constant_matches={i:[j for j,r in enumerate(base) if pair_eq(step[i],r)] for i in ground}
assert all(len(v)==1 for v in constant_matches.values())
# Classify every unordered variable stream pair and every self-pair.
self_rel={i:pair_eq(step[i],step[i]) for i in variable}
assert all(e==('shift',0) for e in self_rel.values())
collisions=[]
for j,i in enumerate(variable):
    for k in variable[j+1:]:
        e=pair_eq(step[i],step[k])
        if e:collisions.append([i,k,list(e)])
base_events=[]
for i in variable:
    for j,b in enumerate(base):
        e=pair_eq(step[i],b)
        if e:base_events.append([i,j,list(e)])
assert all(e[2][0]=='k' and e[2][1]==0 for e in base_events)
shifts=[e for e in collisions if e[2][0]=='shift']
points=[e for e in collisions if e[2][0]=='point']
assert len(shifts)==5 and all(e[2][1]==-1 for e in shifts)
assert len({v for e in shifts for v in e[:2]})==10
assert len(points)==1 and points[0][2][1:]==[0,0]
assert len(base_events)==7
assert all(v in {x[0] for x in base_events} for v in points[0][:2])

# A second, purely concrete, hash-consed ground substitution check.
# This uses constructor tuple identity, not the symbolic equation solver.
ground_nodes=[];intern={}
def mk(tag,*children):
    key=(tag,*children)
    if key not in intern:intern[key]=len(ground_nodes);ground_nodes.append(key)
    return intern[key]
def instantiate(k):
    x=mk('L')
    for _ in range(k):x=mk('S',x)
    out=[]
    for n in nodes:out.append(x if n[0]=='X' else mk(n[0],*(out[i] for i in n[1:])))
    return out
B=instantiate(0)
base_set={(B[r['x']],B[r['y']]) for r in base}
assert len(base_set)==179
U=set(base_set);concrete=[]
for k in range(101):
    T=instantiate(k)
    vs={(T[step[i]['x']],T[step[i]['y']]) for i in variable}
    inc=len(vs-U);inbase=len(vs&base_set)
    U|=vs
    concrete.append({'k':k,'variable_distinct':len(vs),'overlap_base':inbase,'new_calls':inc,'union':len(U)})
    assert len(U)==64*k+241
    assert inc==(62 if k==0 else 64)
receipt={
 'source_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),
 'reachability':reach,'nonoracle_rows':len(nonoracle),'ground_rows':len(ground),'variable_rows':len(variable),
 'ground_step_to_base1':constant_matches,'all_variable_pair_collisions':collisions,'all_variable_to_base1_events':base_events,
 'proof_count':{'base1':179,'variable_at_k0':68,'variable_distinct_base_overlap_at_k0':6,'new_at_k0':62,'new_at_every_k_ge_1':64,'D_n_for_n_ge_2':'64*n+113'},
 'concrete_independent_substitution_checks':concrete,
 'self_pair_count':len(self_rel),'self_pair_relation':'k-l=0',
 'symbolic_pair_checks':len(variable)*(len(variable)-1)//2,
 'variable_base_checks':len(variable)*len(base),
}
Path(__file__).with_name('independent_growth_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('ground_step_to_base1','concrete_independent_substitution_checks')},indent=2))
