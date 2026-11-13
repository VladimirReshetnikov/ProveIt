#!/usr/bin/env python3
"""Read-only graph and all-ring coordinate-identity check for the 79-row probe."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json, random, sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B without optimization')
H = Path(__file__).resolve().parent
D = H.parents[1]
PARENT = D/'research/ten-positive-80-original-kernel-variant/equation.json'
CANDIDATE = H/'candidate.json'
PINS = {PARENT:'90bb24c77fab7a19cd4d021e7cd73eda527f71fc361b0aaba6a5f8eaeb1f7be2',
        CANDIDATE:'5389bb9386371ca71790c5bbac3e5307f4b15ee278e560c13089d65f3ea25d00'}
def sha(p): return sha256(p.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise RuntimeError(msg)
for p,h in PINS.items(): need(sha(p)==h, 'input changed '+str(p))
old=json.loads(PARENT.read_text());new=json.loads(CANDIDATE.read_text())
need(old['operations']==80 and len(old['source'])==80,'parent count')
need(new['operations']==79 and len(new['source'])==79 and new['source_parent_sha256']==PINS[PARENT], 'candidate count/pin')
need(new['witnesses']==['J','F','C','i','T','w','s','n','eta','zeta'], 'witnesses')
need(new['fixed_numerals']==old['fixed_numerals']==['beta','K0','MC','MF'], 'ports')
need(new['output']==old['output']=='N','output')
need(Counter(r[1] for r in new['source'])=={'*':48,'+':17,'-':14},'operation counts')
need(new['operation_breakdown']=={'*':48,'+':17,'-':14},'declared operation counts')

# Verify topology, no duplicate definitions and liveness of every row/input.
known=set(new['witnesses']+new['fixed_numerals']);definitions={}
for row in new['source']:
    need(isinstance(row,list) and len(row)==4,'invalid row')
    name,op,a,b=row
    need(isinstance(name,str) and name not in known and op in ('+','-','*'),'bad row definition')
    for v in (a,b):need((type(v) is int and v>=0) or (isinstance(v,str) and v in known),'unknown/forward operand')
    definitions[name]=(op,a,b);known.add(name)
todo=['N'];live=set();inputs=set()
while todo:
    n=todo.pop()
    if n in live:continue
    if n not in definitions:inputs.add(n);continue
    live.add(n)
    for v in definitions[n][1:]:
        if isinstance(v,str):todo.append(v)
need(live==set(definitions),'dead row')
need(inputs==set(new['witnesses']+new['fixed_numerals']),'dead witness or port')

# The only edits are the eliminated old C row and the two changed G rows.
parent={r[0]:r for r in old['source']};candidate={r[0]:r for r in new['source']}
need(parent['q']==['q','+','bJ',1] and parent['qmF']==['qmF','-','q','F'],'radix shape')
need(parent['C']==['C','-','qmF','alpha'] and parent['G1']==['G1','*','bJ','qmF'] and
     parent['G']==['G','+','G1','alpha'],'parent substitution shape')
need(candidate['G1']==['G1','*','q','qmF'] and candidate['G']==['G','-','G1','C'],'candidate substitution shape')
need([r for r in old['source'] if 'alpha' in r[2:]]==[parent['C'],parent['G']],'unexpected alpha use')
need([r for r in old['source'] if 'G1' in r[2:]]==[parent['G']],'unexpected G1 use')
need(set(parent)-set(candidate)=={'C'} and set(candidate)-set(parent)==set(),'changed node set')
for n,row in parent.items():
    if n not in ('C','G1','G'):need(candidate[n]==row,'unexpected row change '+n)

# Normalize only the small changed region in Z[b,F,C]. A dictionary maps
# exponent triples to integer coefficients. These coefficient equalities
# establish the identities in every commutative ring, without sampling.
def add(a,b,sign=1):
    z=dict(a)
    for mon,c in b.items():z[mon]=z.get(mon,0)+sign*c
    return {m:c for m,c in z.items() if c}
def mul(a,b):
    z={}
    for u,c in a.items():
        for v,d in b.items():
            mon=tuple(x+y for x,y in zip(u,v));z[mon]=z.get(mon,0)+c*d
    return {m:c for m,c in z.items() if c}
one={(0,0,0):1};b={(1,0,0):1};F={(0,1,0):1};C={(0,0,1):1}
q=add(b,one);qmF=add(q,F,-1);alpha=add(qmF,C,-1)
old_C=add(qmF,alpha,-1);old_G=add(mul(b,qmF),alpha)
new_G=add(mul(q,qmF),C,-1)
need(old_C==C and old_G==new_G,'all-ring local polynomial identity failed')
# Every unchanged downstream row receives equal inputs, except the private
# G1 node whose only user is the already-compared G. Induction through the
# verified ordered rows gives equality of the complete output polynomial.

def evaluate(rows,values,modulus):
    values=dict(values)
    for n,op,a,b in rows:
        A=a if type(a) is int else values[a];B=b if type(b) is int else values[b]
        values[n]=({'+' : lambda:A+B, '-' : lambda:A-B, '*' : lambda:A*B}[op]())%modulus
    return values['N']
rng=random.Random(77655);modulus=1000000007
for _ in range(100):
    vals={n:rng.randrange(modulus) for n in new['witnesses']+new['fixed_numerals']}
    previous=dict(vals);previous['alpha']=(vals['beta']*vals['J']+1-vals['F']-vals['C'])%modulus
    need(evaluate(old['source'],previous,modulus)==evaluate(new['source'],vals,modulus),'sample mismatch')
for p,h in PINS.items():need(sha(p)==h,'input changed after check '+str(p))
print(json.dumps({'status':'PASS','operations':79,'breakdown':dict(sorted(Counter(r[1] for r in new['source']).items())),
                  'live_rows':len(live),'live_inputs':len(inputs),'modular_samples':100,
                  'candidate_sha256':sha(CANDIDATE),'parent_sha256':sha(PARENT),
                  'scope':'all-ring identity after affine coordinate substitution; positive-witness converse and iPRA are not proved'},sort_keys=True))
