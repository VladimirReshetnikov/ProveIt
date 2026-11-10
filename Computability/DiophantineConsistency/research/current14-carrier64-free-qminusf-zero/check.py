#!/usr/bin/env python3
"""Finite graph and scalar checks for a symbolic free-(q-F) candidate zero."""
from collections import Counter
import gzip
import hashlib
import json
import math
from pathlib import Path
import random
import sys
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
SOURCE=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PIN='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
providers={
 'research/current14-carrier64-pell-floor/result.json':'8edbf8c5b59d4ba77d2bea5beb54f380bef1b7c1ddb3df8ef98e79c009b8181a',
 'research/current14-carrier64-toy-full-zero/result.json':'04548f6ce0d53ce1c95f97af66e7e400d7357da447cf52751758d9b93f1d8b02'}
for name,digest in providers.items():
    if hashlib.sha256((D/name).read_bytes()).hexdigest()!=digest:raise RuntimeError(f'provider changed: {name}')
raw=SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PIN:raise RuntimeError('source graph pin mismatch')
old=json.loads(raw);rows=[]
for row in old['source']:
    if row[0]=='qF':
        if row!=['qF','-','q','F']:raise RuntimeError('unexpected qF row')
        continue
    rows.append([row[0],row[1]]+['u' if x=='qF' else x for x in row[2:]])
witnesses=['u' if x=='F' else x for x in old['witnesses']]
graph={'schema':'literal_integer_arithmetic_dag_v1','name':'conditional_free_q_minus_F_64',
       'status':'not an established equivalent; current-port symbolic zero construction',
       'source_parent_sha256':PIN,'witness_domain':'strictly positive integers',
       'witnesses':witnesses,'fixed_numerals':old['fixed_numerals'],'source':rows,
       'output':old['output'],'operation_counts':dict(sorted(Counter(x[1] for x in rows).items()))}
if len(rows)!=64 or graph['operation_counts']!={'*':37,'+':16,'-':11}:
    raise RuntimeError('unexpected graph census')
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
    raw=gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:raise RuntimeError('raw mismatch')
    ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length();q=beta+1;hi=mf-beta
if not (beta==(1<<B)-1 and B==94517 and K>0 and 0<lo<beta<mf<2*beta and
        lo%4==2 and hi%8==4 and lo.bit_count()+hi.bit_count()==B):
    raise RuntimeError('current port prerequisites failed')
G0=q*(hi-1)+lo+1;G=G0+q**3;R=G*(q*q-1)+lo+q*mf;N=(R-1)//2
if not ((G0>>B)&1 and R%4==3 and R.bit_count()==3*B+2 and N.bit_count()==3*B+1):
    raise RuntimeError('rank saturation failed')
residue=(R-B)%B;Mmod=(K+(1<<residue))%beta
divisor=math.gcd(Mmod+1,beta);rhs=(Mmod*G+1)%beta
if rhs%divisor:raise RuntimeError('transport congruence insoluble')
period=beta//divisor;representative=((rhs//divisor)*pow((Mmod+1)//divisor,-1,period))%period
lower=G//q+1;upper=(G-1)//beta
u=representative+max(0,(lower-representative+period-1)//period)*period
alpha=G-beta*u;C=u-alpha
if not (lower<=u<=upper and u>q and alpha>0 and C>0 and (Mmod*C+u-1)%beta==0):
    raise RuntimeError('positive scalar solution failed')
def digest(x):return hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest()

def evaluate(rows,values,mod):
    env=dict(values)
    for n,op,a,b in rows:
        x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
        env[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%mod
    return env['polynomial']
rng=random.Random(0xF64)
for _ in range(200):
    v={x:rng.randrange(1,1000) for x in witnesses+old['fixed_numerals']}
    previous=dict(v);previous['F']=v['beta']*v['J']+1-v['u']
    if evaluate(old['source'],previous,1000000007)!=evaluate(rows,v,1000000007):
        raise RuntimeError('full graph substitution control failed')
data=json.dumps(graph,sort_keys=True,indent=2)+'\n'
result={'source_sha256':PIN,'provider_pins':providers,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'graph_sha256':hashlib.sha256(data.encode()).hexdigest(),'operation_counts':graph['operation_counts'],
        'beta_mersenne_exponent':B,'rank_bit_length':R.bit_length(),'rank_mod_4':R%4,
        'rank_population':R.bit_count(),'N_population':N.bit_count(),'w_exponent_residue':residue,
        'transport_coefficient_gcd':divisor,'u_bit_length':u.bit_length(),'u_sha256':digest(u),
        'u_gt_q':True,'alpha_positive':True,'C_positive':True,'transport_congruence':True,
        'modular_graph_substitution_cases':200,
        'scope':'actual-port finite scalar checks; full witness symbolic and external'}
out=json.dumps(result,sort_keys=True,indent=2)+'\n'
if sys.argv[1:]==['--write']:
    (HERE/'graph.json').write_text(data);(HERE/'result.json').write_text(out)
elif sys.argv[1:]==[]:
    if (HERE/'graph.json').read_text()!=data or (HERE/'result.json').read_text()!=out:
        raise RuntimeError('frozen output drift')
    print(out,end='')
else:raise SystemExit('usage: check.py [--write]')
