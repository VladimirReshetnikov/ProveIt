#!/usr/bin/env python3
"""Independent literal-data replay; imports no generator or upstream program."""
import json, math, random
from pathlib import Path
from collections import defaultdict
P=Path(__file__).resolve().parent
D=json.loads((P/'stack_step.json').read_text())
def poly(row):return {tuple(t['monomial']):t['coefficient'] for t in row}
def mul(a,b):
 r=defaultdict(int)
 for x,c in a.items():
  for y,d in b.items():r[tuple(sorted(x+y))]+=c*d
 return {x:c for x,c in r.items() if c}
def evaluate(row,env,p):return sum(c*math.prod(env[x] for x in m) for m,c in row.items())%p
def dag(env,p):
 v=[]
 for n in D['nodes']:
  o,a=n['op'],n['args']
  z=a[0] if o=='const' else env[a[0]] if o=='var' else v[a[0]]+v[a[1]] if o=='add' else v[a[0]]-v[a[1]] if o=='sub' else v[a[0]]*v[a[1]]
  v.append(z%p)
 return v
for suffix in ('','4','16','64'):
 q=json.loads((P/f'stack_step_quartic{suffix}.json').read_text());rows=list(map(poly,q['quadratic_residuals']))
 expected=defaultdict(int)
 for r in rows:
  assert max(map(len,r))<=2
  for m,c in mul(r,r).items():expected[m]+=c
 expected={m:c for m,c in expected.items() if c}
 assert expected==poly(q['quartic_sum_of_squares'])
 assert max(map(len,expected))==4
 assert q['witness_count']==5+len(q['wire_witnesses'])
 for seed in range(40):
  rng=random.Random(seed);p=1000000007
  env={x:rng.randrange(31) for x in ['S','Sp','a','b','c','u','v']};values=dag(env,p)
  for j,w in enumerate(q['wire_witnesses']):
   env[w['name']]=values[w['dag_node']]
   assert evaluate(rows[j],env,p)==0
  assert evaluate(rows[-1],env,p)==values[D['output']]
  assert evaluate(expected,env,p)==values[D['output']]**2%p
  env['q0']=(env['q0']+1)%p
  assert evaluate(rows[0],env,p)!=0
print('PASS four exact sum-of-squares expansions and 160 independent modular graph replays, with mutation controls')
# Independent stack correctness fixtures, testing only the indicated branch.
def cons(h,t):return 1+(h+t)*(h+t+1)//2+t
def I(a,b):return 2*(a+b)*(a+b+1)+4*b
fixtures=[]
for a in range(4):
 for b in range(4):
  for c in range(4):
   v=cons(a,c)
   fixtures.append(('mp',dict(S=cons(I(a,b),v),Sp=cons(b,c),a=a,b=b,c=c,u=0,v=v)))
   fixtures.append(('gen',dict(S=cons(b,c),Sp=cons(I(a,b)+2,c),a=a,b=b,c=c,u=0,v=0)))
for S in range(20):fixtures.append(('axiom',dict(S=S,Sp=cons(0,S),a=0,b=0,c=0,u=0,v=0)))
for branch,env in fixtures:
 values=dag(env,1000000007)
 assert values[D['branches'][branch]]==0
 assert values[D['output']]==0
assert cons(1,0)==2
print('PASS 148 exact-input branch fixtures (modular arithmetic replay) and singleton endpoint')
# A syntax-only safeguard, not a Lean typecheck.
s=(P/'OneStackEquation.lean').read_text()
assert s.count('(')==s.count(')')
assert 'sorry' not in s and '\naxiom ' not in s
print('PASS constructor parenthesis balance; NOT elaboration or kernel compilation')
