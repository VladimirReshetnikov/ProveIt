#!/usr/bin/env python3
"""Independent raw-hat expansion and complete array comparison; inert inputs only."""
from pathlib import Path
import argparse,hashlib,json
from collections import Counter
PARENT='c6456750337b4f87f55918d03760b5759606b772e298d37c0c5df9c92b87b623'
MAP='d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'
def guard(x,s):
 if not x:raise ValueError(s)
def digest(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load(path):
 def pairs(xs):
  d={}
  for k,v in xs:guard(k not in d,'duplicate');d[k]=v
  return d
 def bad(x):raise ValueError(x)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def polyop(o,a,b):
 if o=='*':
  r={}
  for (i,x),c in a.items():
   for (j,y),d in b.items():
    guard(x is None or y is None,'linear raw hats');k=(i+j,x if x is not None else y);r[k]=r.get(k,0)+c*d
 else:
  r=a.copy()
  for k,c in b.items():r[k]=r.get(k,0)+(c if o=='+'else-c)
 return {k:c for k,c in r.items()if c}
def expand(by,n,seeds):
 memo=seeds.copy()
 def go(v):
  if type(v)is int:return {(0,None):v}if v else{}
  if v in memo:return memo[v]
  guard(v in by,'raw expansion boundary')
  _,o,a,b=by[v];memo[v]=polyop(o,go(a),go(b));return memo[v]
 return go(n)
def audit(p):
 known=set(p['free']);count=Counter();by={}
 for n,o,a,b in p['source']:
  guard(n not in known and o in ('+','-','*'),'unique producer')
  guard(all(type(v)is int or v in known for v in (a,b)),'topology');known.add(n);by[n]=[n,o,a,b];count[o]+=1
 todo=[p['output']];live=set()
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:
   live.add(n)
   if n in by:todo+=by[n][2:]
 guard(live==known,'full liveness')
 return {'total':len(by),'M':count['*'],'A':count['+']+count['-']}
def check(old,new,m):
 def w(n):return m.get(n,n)
 ob={r[0]:r for r in old['source']};nb={r[0]:r for r in new['source']}
 before=audit(old);after=audit(new)
 for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires']:guard(old[k]==new[k],'same interface '+k)
 targets=[w('r346'),w('r540')];Q=w('r108')
 changed={n for n in ob.keys()&nb.keys()if ob[n]!=nb[n]};guard(changed==set(targets),'exact two changed retained producers')
 oldids=(ob.keys()-nb.keys())|changed;newids=(nb.keys()-ob.keys())|changed
 guard(len(oldids)==334 and len(newids)==242,'actual two cones')
 for ids,by in [(oldids,ob),(newids,nb)]:
  guard(all(v not in ids or v in targets for n,r in by.items()if n not in ids for v in r[2:]),'private component boundary')
 guard([r for r in old['source']if r[0]not in oldids]==[r for r in new['source']if r[0]not in newids],'surrounding rows identical and ordered')
 hats={w('edge_hat'+str(i))for i in range(98)};seeds={n:{(0,n):1}for n in hats};seeds[Q]={(1,None):1}
 cuts={}
 for n in targets:
  a,b=expand(ob,n,seeds),expand(nb,n,seeds);guard(a==b,'exact complete selector over raw edge hats');cuts[n]=a
 # Bind stronger raw-hat identities to actual inputs of both complete circuits.
 pool={}
 def token(k):
  if k not in pool:pool[k]=len(pool)
  return pool[k]
 inputs={n:token(('port',n))for n in old['free']}
 def run(rows):
  e=inputs.copy()
  for n,o,a,b in rows:
   av,bv=(e[v]if type(v)is str else token(('int',v))for v in (a,b))
   if n in cuts:
    binding=tuple(sorted((i,e[h]if h is not None else -1,c)for(i,h),c in cuts[n].items()))
    e[n]=token(('raw polynomial',e[Q],binding))
   else:e[n]=token((o,av,bv))
  return e
 a,b=run(old['source']),run(new['source']);guard(all(a[n]==b[n]for n in a.keys()&b.keys()),'all retained registers and entire output identity')
 coeff=[]
 for c in old['coefficient_certificates']:
  wire=c['wire'];expected={(i,None):v for i,v in enumerate(c['ascending_coefficients'])if v}
  guard(expand(ob,wire,{Q:{(1,None):1}})==expand(nb,wire,{Q:{(1,None):1}})==expected,'full coefficient word')
  coeff.append(len(c['ascending_coefficients']))
 guard(old['coefficient_component']==new['coefficient_component'],'entire coefficient component literal')
 guard((after['total'],after['M'],after['A'])==(before['total']-92,before['M']-46,before['A']-46),'full savings')
 guard(all(after[k]==new['ledger'][k]for k in after),'claimed ledger')
 guard(old['ledger']['exact_degree']==new['ledger']['exact_degree'],'degree via whole identity')
 return {'variant':new['variant'],'ledger':after,'raw_hat_expanded_terms':[len(cuts[n])for n in targets],'coefficient_entries':sum(coeff),'same_full_polynomial':True,'same_supplied_coordinates':True,'source_sha256':digest(enc(new['source']))}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path,default=Path('/tmp'));g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
 guard(digest((a.root/'matrix193_terminal_power_composition.json').read_bytes())==PARENT,'parent pin');guard(digest((a.root/'matrix193_entry_controller_charts.json').read_bytes())==MAP,'map pin')
 old=load(a.root/'matrix193_terminal_power_composition.json');new=load(a.author_root/'matrix193_selector_block_sharing.json');charts=load(a.root/'matrix193_entry_controller_charts.json')
 for n,h in new['pins'].items():guard(digest((a.root/n).read_bytes())==h,'author dependency '+n)
 guard(new['source_sha256']==digest((a.author_root/'matrix193_selector_block_sharing.py').read_bytes()),'author source binding')
 guard(len(old['packets'])==len(new['packets'])==4 and len(charts['packets'])==3,'inventory')
 result={'checker_sha256':digest(Path(__file__).read_bytes()),'author_pins':{x:digest((a.author_root/('matrix193_selector_block_sharing.'+x)).read_bytes())for x in ('py','json','md')},'packets':[check(o,n,{}if i==0 else charts['packets'][i-1]['map'])for i,(o,n)in enumerate(zip(old['packets'],new['packets']))],'predecessor_execution':False}
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:guard(enc(result)==enc(load(a.expect)),'canonical type-exact receipt')
 print('PASS independent raw-hat selector expansion and complete source identities')
if __name__=='__main__':main()
