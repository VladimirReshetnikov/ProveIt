#!/usr/bin/env python3
"""Bounded source prototype for globally replacing Cantor pairing by dyadic pairing.

P2(a,b)=2**a*(2*b+1)-1. All pair/unpair occurrences are replaced together.
This script measures source sharing and finite macro regressions; it does not
claim a calibrated new proof enumeration or a certified transition table.
"""
import json,itertools
import inverse_mp as q
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
PAIR=z.MACRO[119][1][0]
OUT=q.W/'dyadic_pairing219';OUT.mkdir(exist_ok=True)
def move(a,b,k=1):
 body=q.CI(b)if k==1 else(q.CI(b),q.CI(b))
 return(q.CD(a),(body,q.CC(2)))
def P2(a,b):return 2**a*(2*b+1)-1
def unP2(n):
 a=0
 while n%2:n=(n-1)//2;a+=1
 return a,n//2
m17=move(1,7);m71=move(7,1);d17=move(1,7,2);d71=move(7,1,2)
pairers=[]
# Start at2b and apply n ->2n+1 once for each unit of a.
for order in [(d71,m17,q.CI(7)),(d71,q.CI(7),m17)]:
 for body in q.assocs(order):pairers.append((d17,(q.CD(6),(body,q.CC(2)))))
# Alternatively start at2b+1, double once for each unit of a, subtract1.
double1=d17,m71
loop6=q.CD(6),(double1,q.CC(2))
finish=q.CD(1),m17
pairers.extend(q.assocs((double1,q.CI(1),loop6,finish)))
pairers=list(dict.fromkeys(pairers))
def unpairer(r,swap):
 oddparts=(move(7,r),q.CI(6))if swap else(q.CI(6),move(7,r))
 odd=oddparts,q.CC(3)
 return(q.CD(r),((q.CD(r),(q.CI(7),q.CC(3))),odd))
ups={(r,swap):unpairer(r,swap)for r in(2,8)for swap in(False,True)}
for tr in pairers+list(ups.values()):assert s.boundary(tr)==(0,0,False)
pair_checks=0
for tr in pairers:
 for a,bv in itertools.product(range(7),range(7)):
  rr=[3,bv,5,0,4,9,a,0,8];oo,_=q.sim(tr,rr)
  exp=rr.copy();exp[1]=exp[6]=0;exp[7]=P2(a,bv)
  assert oo==exp,(a,bv,oo,exp);pair_checks+=1
unpair_checks=0
for(r,swap),tr in ups.items():
 for n in sorted(set(range(257))|{2**k-1 for k in range(9,12)}):
  rr=[3,4,5,0,6,9,0,0,8];rr[r]=n;oo,_=q.sim(tr,rr)
  exp=rr.copy();exp[r]=0;exp[6],exp[7]=unP2(n)
  assert oo==exp,(r,swap,n,oo,exp);unpair_checks+=1
records=[];trees=[]
for pi,pair in enumerate(pairers):
 for swap2,swap8 in itertools.product((False,True),repeat=2):
  count={'pair':0,'unpair2':0,'unpair8':0}
  def change(n):
   if n==PAIR:count['pair']+=1;return pair
   if not s.leaf(n)and n[1]==q.ubody and n[0]in(q.CD(2),q.CD(8)):
    r=n[0][1];count['unpair'+str(r)]+=1;return ups[r,swap2 if r==2 else swap8]
   if s.leaf(n):return n
   return change(n[0]),change(n[1])
  tr=change(OLD);assert count=={'pair':174,'unpair2':82,'unpair8':4}
  rows=s.sites(tr);assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
  rec={'pair_variant':pi,'unpair2_swap':swap2,'unpair8_swap':swap8,
       'pair_metrics':s.metrics(pair),'unpair_metrics':s.metrics(ups[2,swap2]),
       'replacement_counts':count,'metrics':s.metrics(tr)}
  records.append(rec);trees.append(tr)
minimum=min(r['metrics']['dag_nodes']for r in records)
best=next(i for i,r in enumerate(records)if r['metrics']['dag_nodes']==minimum)
(OUT/'best_sites.json').write_bytes(s.compact(s.sites(trees[best])))
summary={'status':'GLOBAL_SOURCE_PROTOTYPE_ONLY; NO_MACHINE_OR_PROOF_ENUMERATOR_CALIBRATION',
 'pairing':'P2(a,b)=2**a*(2*b+1)-1','layouts':len(records),
 'pair_variants':len(pairers),'finite_pair_cases':pair_checks,'finite_unpair_cases':unpair_checks,
 'minimum_DAG':minimum,'minimum_DAG_zero6':min((r['metrics']['dag_nodes']for r in records if r['metrics']['maximum_zero_run']<=6),default=None),
 'best_index':best,'compiler_attempted':False,'records':records}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k!='records'}),flush=True)
