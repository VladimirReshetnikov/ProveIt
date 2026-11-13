#!/usr/bin/env python3
"""Finite checks for a symbolic zero of the free-Y 63-gate graph."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import random
import sys
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
providers={
 'research/current14-carrier64-pell-floor/result.json':'8edbf8c5b59d4ba77d2bea5beb54f380bef1b7c1ddb3df8ef98e79c009b8181a',
 'research/current14-carrier64-toy-full-zero/result.json':'04548f6ce0d53ce1c95f97af66e7e400d7357da447cf52751758d9b93f1d8b02'}
for name,h in providers.items():
    if hashlib.sha256((D/name).read_bytes()).hexdigest()!=h:raise RuntimeError('provider pin mismatch')
raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN:raise RuntimeError('source pin mismatch')
old=json.loads(raw);removed={r[0]:r for r in old['source'] if r[0] in ('q3','Y')}
if removed!={'q3':['q3','*','q2','q'],'Y':['Y','*','s','q3']}:
    raise RuntimeError('unexpected removed rows')
rows=[r[:] for r in old['source'] if r[0] not in ('q3','Y')]
witnesses=['Y' if x=='s' else x for x in old['witnesses']]
graph={'schema':'literal_integer_arithmetic_dag_v1','name':'conditional_free_Y_63',
       'status':'not established equivalent; symbolic current-port zero construction',
       'source_parent_sha256':PIN,'witness_domain':'strictly positive integers',
       'witnesses':witnesses,'fixed_numerals':old['fixed_numerals'],'source':rows,
       'output':old['output'],'operation_counts':dict(sorted(Counter(r[1] for r in rows).items()))}
if len(rows)!=63 or graph['operation_counts']!={'*':35,'+':16,'-':12}:
    raise RuntimeError('unexpected operation census')
deps={n:(a,b) for n,_,a,b in rows};live=set();todo=[graph['output']]
while todo:
    x=todo.pop()
    if x not in live:
        live.add(x)
        if x in deps:todo.extend(deps[x])
if any(x not in live for x in witnesses+old['fixed_numerals']+list(deps)):
    raise RuntimeError('dead graph input or gate')
ports={}
for name,meta in old['coefficient_binding']['ports'].items():
    packed=(SOURCE.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256']:raise RuntimeError('gzip mismatch')
    data=gzip.decompress(packed)
    if hashlib.sha256(data).hexdigest()!=meta['raw_sha256']:raise RuntimeError('raw mismatch')
    ports[name]=int.from_bytes(data,'big')
beta,K,lo,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length();q=beta+1;e=88042;C=17
if not (B==94517 and beta==(1<<B)-1 and K>0 and 0<lo<beta<mf<2*beta):
    raise RuntimeError('current port prerequisites failed')
Mbar=(K+(1<<e))%beta;F=(Mbar*C)%beta;alpha=q-F-C
G=beta*(q-F)+alpha;R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
if not (F>0 and alpha>0 and q-F-alpha==C and R>=2*B and R%4==3 and
        (R-B)%B==e and (Mbar*C-F)%beta==0 and R.bit_count()==283450 and
        N.bit_count()-1==283448 and N.bit_count()-1<3*B):
    raise RuntimeError('fixed scalar/valuation checks failed')
def digest(x):return hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest()
def evaluate(rows,values,mod):
    env=dict(values)
    for name,op,left,right in rows:
        a=env[left] if isinstance(left,str) else left;b=env[right] if isinstance(right,str) else right
        env[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()%mod
    return env['polynomial']
rng=random.Random(0xF63);prime=1000000007
for _ in range(200):
    inp={key:rng.randrange(1,1000) for key in witnesses+old['fixed_numerals']}
    qsmall=(inp['beta']*inp['J']+1)%prime
    if not qsmall:raise RuntimeError('control denominator zero')
    previous=dict(inp);previous['s']=inp['Y']*pow(pow(qsmall,3,prime),-1,prime)%prime
    if evaluate(old['source'],previous,prime)!=evaluate(rows,inp,prime):
        raise RuntimeError('full graph substitution mismatch')
data=json.dumps(graph,sort_keys=True,indent=2)+'\n'
result={'source_sha256':PIN,'provider_pins':providers,
 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'graph_sha256':hashlib.sha256(data.encode()).hexdigest(),'operation_counts':graph['operation_counts'],
 'beta_mersenne_exponent':B,'C':C,'w_exponent_residue':e,
 'F_bit_length':F.bit_length(),'F_sha256':digest(F),'alpha_positive':True,
 'rank_bit_length':R.bit_length(),'rank_mod_4':R%4,'rank_population':R.bit_count(),
 'Y_v2_by_pell_floor':N.bit_count()-1,'q_cubed_v2':3*B,'transport_congruence':True,
 'modular_graph_substitution_cases':200,
 'scope':'finite actual-port checks; full free-Y witness symbolic and external'}
out=json.dumps(result,sort_keys=True,indent=2)+'\n'
if sys.argv[1:]==['--write']:
    (HERE/'graph.json').write_text(data);(HERE/'result.json').write_text(out)
elif sys.argv[1:]==[]:
    if (HERE/'graph.json').read_text()!=data or (HERE/'result.json').read_text()!=out:
        raise RuntimeError('frozen output drift')
    print(out,end='')
else:raise SystemExit('usage: check.py [--write]')
