#!/usr/bin/env python3
"""Construct a 77-operation unit-product candidate from the 78 graph.

Finite checks and exact symbolic leading forms are not zero-equivalence proofs.
"""
import hashlib, json, random, runpy, sys
from collections import Counter
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
PARENT=HERE.parent/'p64-qcube78-candidate/graph.json'
PARENT_SHA='8037b90bdeb55c5fe91ab2db7e96b8c200f6c48c3ae6f0902e87435d1f1ba096'
raw=PARENT.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PARENT_SHA: raise RuntimeError('parent graph hash drift')
parent=json.loads(raw)
if len(parent['source'])!=78 or parent['witnesses'][9]!='t': raise RuntimeError('unexpected parent structure')
VERIFY=ROOT/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/verify.py'
if hashlib.sha256(VERIFY.read_bytes()).hexdigest()!='97de6a4ff04997de2c5e0062c4c8b335cf4c8da6b1cd2b85b543948a62e3677b': raise RuntimeError('verifier drift')
classes=runpy.run_path(str(VERIFY)); Poly,Lead=classes['Poly'],classes['Lead']
if classes['identities']()!=4: raise RuntimeError('parent residual identities failed')
tail_expected=[
 ['A0_square','*','A0','A0'], ['M_square','*','M','M'], ['W_square','*','W','W'],
 ['Na_square','*','Na','Na'], ['Lt_square','*','Lt','Lt'],
 ['sum0','+','A0_square','M_square'], ['sum1','+','sum0','W_square'],
 ['sum2','+','sum1','Na_square'], ['sum3','+','sum2','Lt_square'],
 ['polynomial','-','sum3',2]]
if parent['source'][-10:] != tail_expected: raise RuntimeError('unexpected parent tail')
rows=parent['source'][:-10]+[
 ['unit_product','*','A0','Na'], ['unit_minus_one','-','unit_product',1],
 ['unit_square','*','unit_minus_one','unit_minus_one'],
 ['M_square','*','M','M'], ['W_square','*','W','W'], ['Lt_square','*','Lt','Lt'],
 ['sum0','+','unit_square','M_square'], ['sum1','+','sum0','W_square'],
 ['polynomial','+','sum1','Lt_square']]
witnesses=parent['witnesses']; ports=parent['fixed_numerals']
known=set(witnesses+ports); deps={}
for name,op,x,y in rows:
    if name in known or op not in ('+','-','*') or any(not isinstance(v,int) and v not in known for v in (x,y)): raise RuntimeError('invalid or non-topological gate: '+str(name))
    known.add(name); deps[name]=[v for v in (x,y) if isinstance(v,str)]
seen,todo=set(),[parent['output']]
while todo:
    name=todo.pop()
    if name in seen: continue
    seen.add(name); todo.extend(deps.get(name, []))
if len(rows)!=77 or len(seen.intersection(deps))!=77 or not set(witnesses+ports)<=seen: raise RuntimeError('unexpected gate/input liveness')
if rows[:-9]!=parent['source'][:-10]: raise RuntimeError('unchanged rows differ')
count=dict(Counter(row[1] for row in rows))
a,n=Poly.var('a'),Poly.var('n')
unit=(a*n-1)**2
if unit != a*a*n*n-2*a*n+1: raise RuntimeError('unit-factor identity')
# Exact leading-form computation using the same expanded main/auxiliary
# residual identities as the pinned P64 verifier.
v={n:Lead.var(n) for n in witnesses}; v.update({n:Lead.var(n,0) for n in ports})
J,F,alpha,z,f,i,T,s,w,t,eta,zeta,e,gamma=[v[n] for n in witnesses]
beta,K0,MC,MF=[v[n] for n in ports]
q=beta*J+1; Y=q**3*s; X=w*q; E=X*Y; k=eta+zeta
c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H; ell=E*k*Y
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
r=k-R-1; U=Y*Y; I=i*c*c; Aaux=Delta*(f*f-1)
V=f*f*(c*T-R)-c
A0=t*t-ell*(ell+k)
D0=X+a*c+H*gamma
D0gap=2*a*c*(X+H*gamma)+(X+H*gamma)**2-H*c*c-1
M=U*U*D0gap-2*U*H*r*D0+H*H*r*r
W=I*I-Aaux; Na=V*V-(Aaux-1)*e*(2*V+e)
Lt=(K0+w)*(q-F-alpha)-F-z*(q-1)
output=(A0*Na-1)**2+M*M+W*W+Lt*Lt
expected=4*Poly.var('beta')**50*Poly.var('J')**50*Poly.var('T')**2*Poly.var('e')**2*Poly.var('f')**8*Poly.var('s')**14*Poly.var('w')**8*(Poly.var('eta')+Poly.var('zeta'))**6
if output.degree!=90 or output.p!=expected: raise RuntimeError('unexpected degree or leading form')
def evaluate(graph_rows,initial,modulus):
    values={key:value%modulus for key,value in initial.items()}
    def get(v): return v%modulus if isinstance(v,int) else values[v]
    for name,op,x,y in graph_rows:
        a,b=get(x),get(y)
        values[name]={'+':lambda:(a+b)%modulus,'-':lambda:(a-b)%modulus,'*':lambda:(a*b)%modulus}[op]()
    return values
rng=random.Random(0x7790); checks=0
for modulus in (1000003,1000033,1000037):
    for _ in range(200):
        sample={n:rng.randrange(1,modulus) for n in witnesses+ports}
        old=evaluate(parent['source'],sample,modulus); new=evaluate(rows,sample,modulus)
        expected_output=((old['A0']*old['Na']-1)**2+old['M']**2+old['W']**2+old['Lt']**2)%modulus
        if any(old[n]!=new[n] for n in ('A0','M','W','Na','Lt')) or new['polynomial']!=expected_output:
            raise RuntimeError('graph residual/output formula mismatch')
        checks+=1
graph={'name':'p64_qcube_unit_positive14_degree90','witness_domain':'strictly positive integers',
       'witnesses':witnesses,'fixed_numerals':ports,'source':rows,'output':parent['output'],
       'operations':len(rows),'operation_counts':count,'exact_degree':90,
       'status':'candidate; zero-existence equivalence and iPRA endpoint unproved','parent_graph_sha256':PARENT_SHA}
metrics={'status':'PASS_FINITE_AND_SYMBOLIC_CHECKS_ONLY','parent_sha256':PARENT_SHA,
         'builder_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'operations':len(rows),'operation_counts':count,'live_gates':len(seen.intersection(deps)),
         'witnesses':len(witnesses),'degree':90,
         'residual_degrees':{n:x.degree for n,x in [('A0',A0),('M',M),('W',W),('Na',Na),('Lt',Lt)]},
         'leading_form':output.p.json(),
         'leading_form_condition':'beta != 0','parent_residual_identities':4,'exact_unit_factor_identity':True,
         'unchanged_parent_rows':len(rows)-9,'modular_graph_samples':checks,
         'scope':'Finite graph checks and symbolic leading forms; no zero-existence or iPRA equivalence.'}
outputs=[(HERE/'graph.json',json.dumps(graph,indent=2)+'\n'),(HERE/'checks.json',json.dumps(metrics,indent=2,sort_keys=True)+'\n')]
if sys.argv[1:]==['--write']:
    for path,_ in outputs:
        if path.exists(): raise SystemExit(f'refusing to overwrite {path}')
    for path,text in outputs: path.write_text(text)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B build.py [--write]')
else:
    for path,text in outputs:
        if path.read_text()!=text: raise SystemExit(f'generated bytes differ: {path}')
print(json.dumps({k:metrics[k] for k in ('status','operations','operation_counts','degree','residual_degrees','modular_graph_samples')},sort_keys=True))
