#!/usr/bin/env python3
"""Emit V and NK separately; discard precisely V on either freshness collision.

The guard uses the fact that NK=I(K,1) is positive. Clearing TW is an
idempotent failure mark; each guarded cleanup therefore pops at most once.
"""
import itertools,json,time
from pathlib import Path
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'split_bundle219';OUT.mkdir(exist_ok=True)
CI=q.CI;CD=q.CD;CC=q.CC;CB=q.CB
pop=z.MACRO[119][0]
C1=(CD(1),CC(1));C5=(CD(5),CC(1));C6=(CD(6),CC(1))
move61=(CD(6),(CI(1),CC(2)))
move65=(CD(6),(CI(5),CC(2)))
pop5=(pop,move65)
E=s.subtree(OLD,'111110');EA=(E,C1)
GATE='111010010011101111';gate=s.subtree(OLD,GATE)
copyc=s.subtree(OLD,q.x.at_interval(OLD,4563,4567))
# Exact syntactic removal of the final builder I, retaining the outer N.
FINAL='1110100100111011100';fin=s.subtree(OLD,FINAL)
assert fin==(z.MACRO[119],z.MACRO[218])
without=s.replace(OLD,FINAL,fin[1])

def replacement(n,action):
 if n==EA:return(E,action)
 if s.leaf(n):return n
 return(replacement(n[0],action),replacement(n[1],action))
cleanup={}
for name,parts in [('clear_pop6',(C1,pop,C6)),('pop6_clear',(pop,C6,C1)),('pop1_clear',(pop,move61,C1)),('pop5_clear',(pop5,C5,C1))]:
 for k,body in enumerate(q.assocs(parts)):cleanup[f'{name}_a{k}']=(CD(1),body)
cleanup.update({'pop_clear_E':(CD(1),((pop,C1),E)),
                'clear_pop_E':(CD(1),((C1,pop),E)),
                'pop_clearE':(CD(1),(pop,(C1,E))),
                'clear_popE':(CD(1),(C1,(pop,E)))})

def checks(gg):
 count=0
 for a,bv,c,V,rest in itertools.product(range(3),range(3),range(3),range(3),range(2)):
  for nk in[1,4,8]:
   rr=[7,nk,(V+rest)*(V+rest+1)//2+rest,c,a,bv,0,0,5]
   oo,_=q.sim((copyc,gg),rr)
   exp=rr.copy();exp[3]=exp[4]=exp[5]=exp[6]=exp[7]=0
   if c in(a,bv):exp[1]=0;exp[2]=rest
   assert oo==exp,(a,bv,c,V,rest,nk,oo,exp)
   count+=1
 return count
results=[];best=999
for name,action in cleanup.items():
 gg=replacement(gate,action)
 try:count=checks(gg)
 except (AssertionError,RuntimeError)as exc:print('REJECT',name,str(exc)[:300],flush=True);continue
 tr=s.replace(without,GATE,gg);m=s.metrics(tr)
 rec={'name':name,'metrics':m,'gate_contract_cases':count,'status':'SOURCE_MACRO_CONTRACT_CHECKED; ENUMERATOR_COMPLETENESS_AND_RUNTIME_SEPARATE'}
 dd=OUT/name;dd.mkdir(exist_ok=True);rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 (dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
# One cleanup after both comparisons: preserve positive NK, otherwise pop V.
for k,discard in enumerate(q.assocs((pop,C6))):
 zero_test=(CD(1),(CI(1),CB(1)))
 post=(zero_test,discard)
 gg=(gate,post)
 try:count=checks(gg)
 except (AssertionError,RuntimeError)as exc:print('REJECT_POST',str(exc)[:300],flush=True);continue
 tr=s.replace(without,GATE,gg);rr=s.sites(tr);m=s.metrics(tr)
 rec={'name':f'post{k}','metrics':m,'gate_contract_cases':count,'status':'SOURCE_MACRO_CONTRACT_CHECKED; ENUMERATOR_COMPLETENESS_AND_RUNTIME_SEPARATE'}
 dd=OUT/rec['name'];dd.mkdir(exist_ok=True);(dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(json.dumps(rec),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
