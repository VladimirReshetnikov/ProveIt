#!/usr/bin/env python3
"""Compose two frozen exact rewrites, reading all predecessors as inert data."""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_entry_shared_coefficient_scout.py':'e5223ccc69d6c42fff7b5fadfae29fa1d9039d513967f27ed0cb48a8e9fb4bee',
 'matrix193_entry_shared_coefficient_scout.json':'a59d1a571695a028d96947d4e2ccd0566af763b272dc170a11d7d1fb92c1c04c',
 'matrix193_entry_shared_coefficient_scout.md':'80bdcde5242044365bdcc904d42964c8d083b3a41e894694e438b60da6b51f70',
 'matrix193_controller_flow_scout.py':'9d9a2dbd121d73a1aee8a34c462db203d9cfd47c42d8302bddf2e602e1dfc49b',
 'matrix193_controller_flow_scout.json':'766d4a77c9c7cfe97dd1131e8c9df9dfa62892206d82fc2d609b9e10b838793e',
 'matrix193_controller_flow_scout.md':'dcc21d29f0bad6f8c07cb3bb5a88831bd127c01f9b6ac4ffd4169265b275269f'}
def ck(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)

def local_identity():
 def add(a,b,s=1):
  r=a.copy()
  for e,v in b.items():r[e]=r.get(e,0)+s*v
  return {e:v for e,v in r.items() if v}
 def mul(a,b):
  r={}
  for e,v in a.items():
   for f,w in b.items():
    g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,0)+v*w
  return {e:v for e,v in r.items() if v}
 one={(0,0,0,0):1};B,J,EL,ES=[{tuple(int(j==k) for j in range(4)):1} for k in range(4)]
 bm=add(B,one,-1);P=add(mul(bm,J),one);dst=add(J,EL,-1)
 old=add(add(add(dst,ES,-1),P),mul(B,dst),-1)
 new=add(add(mul(bm,EL),one),ES,-1)
 ck(old==new,'exact integer polynomial residual identity')
 return {'indeterminates':['B','J','EL','ES'],'ascending_terms':[[list(k),v] for k,v in sorted(new.items())],
         'identity':'(J-EL-ES)+((B-1)*J+1)-B*(J-EL)=1+(B-1)*EL-ES'}

def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports');deps={};ct=Counter();degrees={v:int(v not in p['fixed_numerals']) for v in known}
 for n,op,l,r in p['source']:
  ck(n not in known and op in ['+','-','*'],'unique valid producer')
  ck(all(type(v)is int or type(v)is str and v in known for v in (l,r)),'source topology')
  known.add(n);deps[n]=(l,r);ct[op]+=1
  degrees[n]=degrees.get(l,0)+degrees.get(r,0) if op=='*' else max(degrees.get(l,0),degrees.get(r,0))
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'all paid rows and supplied ports live')
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),
         'residuals':len(p['comparisons']),'literal_count':len({v for row in p['source'] for v in row[2:] if type(v)is int}),
         'all_live':True,'exact_degree':35587,'syntactic_degree_upper':degrees[p['output']]}

def transform(parent,flow,flow_edit):
 for k in ['free','witnesses','fixed_numerals','ports','native_cut_bindings','output']:
  ck(parent[k]==flow[k],'common parent interface '+k)
 packing=flow['stage_counts']['packing'];ck(packing==830,'actual packing stage')
 ck(parent['source'][:packing+63]==flow['source'][:packing+63],'complete shared packing/native prefix')
 by={r[0]:r for r in parent['source']};B=parent['ports']['B'];J=parent['ports']['J'];P=parent['ports']['P'];EL,ES=parent['ports']['raw_edges']
 ck(by[P][1]=='+' and by[P][3]==1,'P affine definition');product=by[P][2]
 ck(by[product][1]=='*' and by[product][3]==J,'P product');bm=by[product][2];ck(by[bm][1:]==['-',B,1],'paid B-1')
 left,right=parent['comparisons'][18];ck(by[left][1]=='+' and by[left][3]==P,'flow left');src=by[left][2]
 ck(by[src][1]=='-' and by[src][3]==ES,'flow source');dst=by[src][2]
 ck(by[dst][1:]==['-',J,EL] and by[right][1:]==['*',B,dst],'flow destination and right')
 gone={dst,src,left,right};tail=parent['source'][-62:];residual=tail[36][0];ck(tail[36][1:]==['-',left,right],'paid residual position')
 removed=[r for r in parent['source'] if r[0] in gone]
 added=[['flow_scaled_load','*',bm,EL],['flow_switch_position','+','flow_scaled_load',1]]
 ck(removed==flow_edit['removed_rows'] and added==flow_edit['new_rows'] and residual==flow_edit['residual_wire'],'same exact frozen flow edit')
 ck(all(row[0] not in by and row[0] not in parent['free'] for row in added),'fresh producer names')
 rows=[];inserted=False
 for row in parent['source']:
  if row[0] in gone:
   if not inserted:rows.extend(added);inserted=True
   continue
  if row[0]==residual:rows.append([residual,'-','flow_switch_position',ES])
  else:
   ck(all(v not in gone for v in row[2:]),'removed cone private');rows.append(row[:])
 keys=['free','witnesses','fixed_numerals','output','ports','native_cut_bindings','comparisons','extraction','fixture_fixed_bindings','coefficient_component','component_ledger','coefficient_certificates']
 p={k:copy.deepcopy(parent[k]) for k in keys};p['source']=rows;p['comparisons'][18]=['flow_switch_position',ES]
 for k in ['n','m','L','padding','groups']:p[k]=copy.deepcopy(flow[k])
 p['name']='uniform_entry_and_flow';p['stage_counts']={'packing':packing,'native':63,'outer_producers':len(rows)-packing-63-62,'finalizer':62};p['ledger']=graph(p)
 ck((p['ledger']['total'],p['ledger']['M'],p['ledger']['A'],len(p['witnesses']))==(1622,791,831,146),'complete actual count')
 ck(p['source'][packing:packing+63]==parent['source'][packing:packing+63],'all63 native rows literal')
 newby={r[0]:r for r in rows}
 ck(all(newby[row[0]]==row for row in parent['coefficient_component']),'all578 coefficient rows retained')
 ck(p['source'][-62:]==[[residual,'-','flow_switch_position',ES] if r[0]==residual else r for r in tail],'entire finalizer edit')
 return p,{'removed_rows':removed,'new_rows':added,'residual_wire':residual,'proved_local_identity':local_identity(),'native_rows_literal':63,'coefficient_rows_literal':len(parent['coefficient_component']),'finalizer_rows':62}

def full_identity(parent,p,proof):
 cache={}
 def ident(k):
  if k not in cache:cache[k]=len(cache)
  return cache[k]
 def run(q):
  env={x:ident(('free',x)) for x in q['free']}
  for n,op,l,r in q['source']:
   a=ident(('constant',l)) if type(l)is int else env[l];b=ident(('constant',r)) if type(r)is int else env[r]
   env[n]=ident(('proved-equal-flow',)) if n==proof['residual_wire'] else ident((op,a,b))
  return env
 a,b=run(parent),run(p);removed={r[0] for r in proof['removed_rows']};kept=0
 for n,op,l,r in parent['source']:
  if n not in removed:ck(a[n]==b[n],'entire retained expression '+n);kept+=1
 ck(kept==1620 and a[parent['output']]==b[p['output']],'complete output identity')
 for label,v in parent['native_cut_bindings'].items():ck(a[v]==b[p['native_cut_bindings'][label]],'all native inputs')
 for j in range(20):ck(a[parent['source'][-62+2*j][0]]==b[p['source'][-62+2*j][0]],'every residual')
 return {'all_ring_relation':'F1622=F1624 on identical supplied coordinates','retained_parent_rows':kept,'native_inputs':6,'native_rows':63,'outer_residuals':20,'finalizer_rows':62,'positive_map':'identity'}

def evaluate(p,v,prime):
 e=dict(v)
 for n,op,l,r in p['source']:
  a=e[l] if type(l)is str else l;b=e[r] if type(r)is str else r
  e[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%prime
 return e
def samples(parent,p):
 rng=random.Random(1622);out=[]
 for prime in [1000000007,1000000009]:
  for k in range(16):
   v={x:rng.randrange(-100,101) for x in p['free']}
   if k%2==0:v.update(p['fixture_fixed_bindings'])
   a,b=evaluate(parent,v,prime),evaluate(p,v,prime)
   for n in a.keys()&b.keys():ck(a[n]==b[n],'retained modular wire '+n)
   ck(a[parent['output']]==b[p['output']],'complete modular value')
   out.append({'prime':prime,'case':k,'saved_fixed_binding':k%2==0,'output':b[p['output']]})
 return out

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 entry=read(root/'matrix193_entry_shared_coefficient_scout.json');flow=read(root/'matrix193_controller_flow_scout.json')
 for stem,r in [('matrix193_entry_shared_coefficient_scout',entry),('matrix193_controller_flow_scout',flow)]:ck(r['source_sha256']==PINS[stem+'.py'],'parent self source pin')
 old=entry['packet'];p,edit=transform(old,flow['packets'][1],flow['full_identities'][1]);identity=full_identity(old,p,edit)
 ck(old['ledger']['degree']==flow['packets'][1]['ledger']['proved_exact_degree']==35587,'common exact degree')
 diagnostic=flow['packets'][0]
 return {'schema':'matrix193-entry-flow-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'status':'PASS','packet':p,'literal_edit':edit,'complete_identity':identity,'modular_checks':samples(old,p),
         'degree_proof':{'exact':35587,'method':'complete polynomial identity to frozen entry-shared1624; inherited bounded-high SWITCH noncancellation'},
         'inherited_diagnostic':{'source_sha256':sha(enc(diagnostic['source'])),'ledger':diagnostic['ledger'],'source_emitted_here':False,'replayed_here':False},
         'scope':{'predecessor_code_executed':False,'supplied_coordinates_changed':False,'new_native_or_giant_outer_fixture':False,'universal84_unchanged':True}}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact type-sensitive receipt')
 print('PASS: complete1622=791M+831A/146w;all retained rows,63 native rows,20 residuals,62 finalizer rows')
