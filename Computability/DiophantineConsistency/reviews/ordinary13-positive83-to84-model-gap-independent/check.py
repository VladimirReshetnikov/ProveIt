#!/usr/bin/env python3
"""Independent pinned graph, carrier and conditional Pell-bound controls."""
from pathlib import Path
import hashlib,itertools,json,random
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
r=ROOT/'research';a=json.loads((r/'ordinary13-qcube-main83/candidate.json').read_text());b=json.loads((r/'ordinary13-qcube-unscale84/candidate.json').read_text())
assert len(a['source'])==83 and len(b['source'])==84
assert a['witnesses'][6]=='w' and b['witnesses'][6]=='X'
assert a['witnesses'][:6]+a['witnesses'][7:]==b['witnesses'][:6]+b['witnesses'][7:]
assert a['fixed_numerals']==b['fixed_numerals']
ra={row[0]:row for row in a['source']};rb={row[0]:row for row in b['source']}
assert set(ra)-set(rb)=={'X'} and set(rb)-set(ra)=={'g55','g56'}
for n in ra.keys()&rb.keys():
 if n!='shift':assert ra[n]==rb[n],n
assert ra['X']==['X','*','q','w'] and rb['g55']==['g55','*','E','q']
assert rb['g56']==['g56','+','g54','g55']
assert ra['shift']==['shift','-','g54','r0'] and rb['shift']==['shift','-','g56','r0']
# Both graph evaluations use the exact same ports and valuation except w/X and gamma.
prime=1000003
def evalgraph(g,e):
 e={k:v%prime for k,v in e.items()}
 for n,op,x,y in g['source']:
  u=x if isinstance(x,int) else e[x];v=y if isinstance(y,int) else e[y]
  e[n]={'+':lambda:u+v,'-':lambda:u-v,'*':lambda:u*v}[op]()%prime
 return e
rng=random.Random(83084)
for _ in range(350):
 env={n:rng.randrange(1,7) for n in a['witnesses']};env.update({n:rng.randrange(0,7) for n in a['fixed_numerals']})
 q=1+env['J']*env['beta'];w=env['w'];g_old=env['gamma'];env['gamma']=g_old+w
 env84={n:env[n] for n in b['witnesses'] if n not in ('X','gamma')};env84.update({n:env[n] for n in b['fixed_numerals']});env84.update({'X':q*w,'gamma':g_old})
 x,y=evalgraph(a,env),evalgraph(b,env84)
 assert all(x[k]==y[k] for k in ('A0','A1','Fa','g72','out'))
# Test conditional source inequality from actual Pell recurrence at R≥3.
def coords(a,R):
 d,c=1,0
 for _ in range(R):d,c=(a+2)*d+(a+1)*(a+3)*c,d+(a+2)*c
 return d,c
count=0
for a,R,X,w,W in itertools.product(range(8),range(3,7),range(8),range(8),range(4)):
 if X>a or w>a:continue
 H=4*a+3;d,c=coords(a,R);num=d+H*W-X-a*c
 assert c> X+H*w and d>(a+1)*c
 if num<0 or num%H:continue
 gamma=num//H
 assert d+H*W==X+a*c+H*gamma and gamma>w
 count+=1
assert count>0
# Rank-two control is fact-level only; not claimed to be an 83 graph zero.
a=4;d,c=coords(a,2);X=w=4;W=0;gamma=1;H=4*a+3
assert d+H*W==X+a*c+H*gamma and not w<gamma
assert (3*8)%3==0 and 8%3!=0 and 1-2<0
print(json.dumps({'source_pins':pins,'exact_row_delta':True,'finite_graph_substitution_controls':350,
 'conditional_pell_balance_controls':count,'rank2_fact_level_counterexample':True,
 'three_cancellation_control':{'q':3,'X':8},'lean_executed':False,
 'scope':'source/math audit only; all graph maps and providers remain unelaborated'},sort_keys=True,indent=2))
