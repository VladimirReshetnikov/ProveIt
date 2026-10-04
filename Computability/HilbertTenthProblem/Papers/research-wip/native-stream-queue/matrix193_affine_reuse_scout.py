#!/usr/bin/env python3
"""Fresh one-gate affine reuse in the complete actual matrix polynomial.
Only inert predecessor bytes and JSON are read; no predecessor execution/import.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_entry_flow_scout.py':'0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf',
 'matrix193_entry_flow_scout.json':'321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da',
 'matrix193_entry_flow_scout.md':'5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def pa(a,b,sgn=1):
 d=dict(a)
 for i,v in b.items():d[i]=d.get(i,0)+sgn*v
 return {i:v for i,v in d.items() if v}
def pm(a,b):
 d={}
 for i,x in a.items():
  for j,y in b.items():d[i+j]=d.get(i+j,0)+x*y
 return {i:v for i,v in d.items() if v}
def polys(p,cut):
 env={cut:{1:1}}
 def val(v):return {0:v} if type(v)is int and v else {} if type(v)is int else env[v]
 for n,o,a,b in p['source']:
  if n==cut:continue
  if all(type(v)is int or v in env for v in (a,b)):
   aa=val(a);bb=val(b);env[n]=pm(aa,bb) if o=='*' else pa(aa,bb,1 if o=='+' else -1)
 return env

def edit(parent):
 by={r[0]:r for r in parent['source']}
 ck(by['r181']==['r181','+','r144',1],'paid affine packing value')
 ck(by['cp373']==['cp373','*',-25,'r144'],'old scalar multiplication')
 ck(by['cp374']==['cp374','+','cp373',-25],'old affine addition')
 users=[n for n,o,a,b in parent['source'] if 'cp373' in (a,b)];ck(users==['cp374'],'only private consumer')
 component={r[0] for r in parent['coefficient_component']};ck({'cp373','cp374'}<=component and 'r181' not in component,'cross-component paid reuse')
 child=copy.deepcopy(parent);replacement=['cp374','*',-25,'r181']
 child['source']=[replacement if r[0]=='cp374' else r for r in parent['source'] if r[0]!='cp373']
 child['coefficient_component']=[replacement if r[0]=='cp374' else r for r in parent['coefficient_component'] if r[0]!='cp373']
 old=polys(parent,'r144');new=polys(child,'r144');ck(old['cp374']==new['cp374']=={1:-25,0:-25},'exact local affine identity')
 return child,{'formal_cut':'t=r144','paid_shared_value':'r181=t+1','old_output':'(-25*t)-25','new_output':'-25*(t+1)','ascending_coefficients':[-25,-25],'deleted_row':by['cp373'],'changed_row_before':by['cp374'],'changed_row_after':replacement,'deleted_private_consumer_count':len(users)}

def audit_source(p):
 known=set(p['free']);deps={};degree={n:0 if n in p['fixed_numerals'] else 1 for n in p['free']}
 for n,o,a,b in p['source']:
  ck(o in ['+','-','*'] and n not in known,'unique valid producer');ck(all(type(v)is int or v in known for v in (a,b)),'topological source')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if o=='*' else max(da,db)
  known.add(n);deps[n]=(a,b)
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'all paid rows and free ports live')
 count=Counter(r[1] for r in p['source']);component=Counter(r[1] for r in p['coefficient_component'])
 p['ledger'].update(total=len(p['source']),M=count['*'],A=count['+']+count['-'],all_live=True,syntactic_degree_upper=degree[p['output']],literal_count=len({v for r in p['source'] for v in r[2:] if type(v)is int}))
 p['component_ledger']={'total':len(p['coefficient_component']),'M':component['*'],'A':component['+']+component['-']}
 p['stage_counts']['outer_producers']-=1
 ck((p['ledger']['total'],p['ledger']['M'],p['ledger']['A'])==(1621,791,830),'complete literal count')
 ck(p['component_ledger']=={'total':577,'M':329,'A':248},'live component count')
 ck(sum(p['stage_counts'].values())==len(p['source']),'complete stage count')

def coefficient_identity(parent,p):
 a=polys(parent,parent['ports']['Q']);b=polys(p,p['ports']['Q']);cert=[]
 for rec in p['extraction']:
  for col,prod in enumerate(rec['products']):
   n=prod['polynomial'];wanted={rec['length']-1-i:c for i,c in enumerate(prod['coefficients']) if c};ck(a[n]==b[n]==wanted,'full coefficient polynomial')
   cert.append({'side':rec['side'],'column':col,'output':n,'degree':max(wanted),'ascending_coefficients':[wanted.get(i,0) for i in range(max(wanted)+1)],'sha256':sha(json.dumps(sorted(wanted.items()),separators=(',',':')).encode())})
 return cert

def complete_identity(parent,p):
 cache={}
 def ident(key):
  if key not in cache:cache[key]=len(cache)
  return cache[key]
 common={n:ident(('free',n)) for n in p['free']};cut=ident(('proved_affine_cut','cp374'))
 def run(src):
  env=dict(common)
  for n,o,a,b in src:
   ai=env[a] if type(a)is str else ident(('integer',a));bi=env[b] if type(b)is str else ident(('integer',b));env[n]=cut if n=='cp374' else ident((o,ai,bi))
  return env
 a=run(parent['source']);b=run(p['source']);names=[r[0] for r in p['source']]
 for n in names:ck(a[n]==b[n],'entire retained register '+n)
 ck(a[parent['output']]==b[p['output']],'complete output identity')
 ck(parent['free']==p['free'] and parent['witnesses']==p['witnesses'],'unchanged full supplied interface')
 return {'all_retained_paid_registers':len(names),'native_rows_retained':parent['stage_counts']['native'],'unchanged_paid_output':p['output'],'all_ring_identity':'F1621 = F1622 on identical supplied coordinates','entire_output_identity':True}

def evaluate(p,v,m):
 env=dict(v)
 for n,o,a,b in p['source']:
  aa=env[a] if type(a)is str else a;bb=env[b] if type(b)is str else b;env[n]=(aa*bb if o=='*' else aa+bb if o=='+' else aa-bb)%m
 return env

def modular_checks(parent,p):
 rng=random.Random(1621);out=[]
 for mod in [1000000007,1000000009]:
  for k in range(8):
   v={n:rng.randrange(-100,101) for n in p['free']}
   if k%2==0:v.update(p['fixture_fixed_bindings'])
   a=evaluate(parent,v,mod);b=evaluate(p,v,mod)
   for n,o,l,r in p['source']:ck(a[n]==b[n],'whole-source modular comparison')
   out.append({'modulus':mod,'case':k,'fixture_fixed_ports':k%2==0,'output':b[p['output']]})
 return out

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 parent_receipt=parse(root/'matrix193_entry_flow_scout.json');ck(parent_receipt['source_sha256']==PINS['matrix193_entry_flow_scout.py'],'parent source/receipt pin');parent=parent_receipt['packet'];p,local=edit(parent);audit_source(p)
 p['coefficient_certificates']=coefficient_identity(parent,p);same=complete_identity(parent,p)
 ck(p['ledger']['exact_degree']==35587 and len(p['witnesses'])==146,'inherited domain and degree')
 return {'schema':'matrix193-affine-reuse-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'scope':{'predecessor_code_executed':False,'same_complete_polynomial':True,'same_146_positive_witnesses':True,'ordinary_input_and_fixed_program_recipe_unchanged':True,'established_universal84_unchanged':True,'IDLE_change':False,'diagnostic_emitted_or_replayed':False,'new_outer_history_or_native_Pell_tuple':False,'minimality_claim':False},'local_identity':local,'complete_identity':same,'packet':p,'modular_checks':modular_checks(parent,p),'degree_proof':{'exact_degree':35587,'reason':'entire polynomial equals the pinned entry-flow parent on identical variables; the inherited uniform bounded-high degree proof transfers'},'inherited_diagnostic':{'status':'unchanged, not emitted or replayed in this packet','reference':'pinned entry-flow parent metadata'}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root)
 if a.write:a.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,parse(a.expect)),'exact typed receipt mismatch')
 print('PASS: complete1621=791M+830A;577-row coefficient component;146w;all-value identity;degree35587')
if __name__=='__main__':main()
