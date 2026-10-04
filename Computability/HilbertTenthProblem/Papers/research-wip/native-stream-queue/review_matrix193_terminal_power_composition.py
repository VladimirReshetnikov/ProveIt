#!/usr/bin/env python3
"""Independent inert-source check of terminal-carry/power composition."""
import argparse,hashlib,json
from pathlib import Path
from collections import Counter
AUTH={'py':'2dc0fb36f50da402cc479673bb2c23a4354f9a80e23fb6f17857168fc1ad9cd1','json':'c6456750337b4f87f55918d03760b5759606b772e298d37c0c5df9c92b87b623','md':'7ea837d4def42b7b97577c3e5f4c421f73a8256ac1858890bdbcc2ad0a6948a3'}
PARENT='6afa10fee956f9e26167345300d886116374dafc6695e91bf5dd3d28679915f2'
RECIPE='c3f525e806cfb3743ff99456b006f23f441091804e85db19cdcb5552859d4006'
C=2**93
def require(x,s):
 if not x:raise ValueError(s)

def digest(b):return hashlib.sha256(b).hexdigest()

def canonical(o):return json.dumps(o,sort_keys=True,separators=(',',':')).encode()

def load(p):
 def obj(pairs):
  d={}
  for k,v in pairs:
   require(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)

def same(a,b):
 if type(a)!=type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def final(p):
 by={r[0]:r for r in p['source']};out=by[p['output']]
 require(out[1]=='-' and out[3]==1,'output minus one')
 prod=by[out[2]];require(prod[1]=='*','native times outer')
 native=prod[2];one=by[prod[3]];require(one[1]=='+' and one[3]==1,'one plus squares')
 names={out[0],prod[0],one[0]};leaves=[]
 def visit(n):
  r=by[n];names.add(n)
  if r[1]=='*':
   require(r[2]==r[3] and type(r[2])is str,'square leaf')
   names.add(r[2]);leaves.append((r[2],n));return
  require(r[1]=='+' and type(r[2])is str and type(r[3])is str,'addition tree')
  visit(r[2]);visit(r[3])
 visit(one[2]);res=[r for r,_ in leaves]
 require(len(set(res))==len(res) and res==p['retained_residual_wires'],'residual inventory')
 require(len(names)==3*len(res)+2,'private complete finalizer size')
 require(all(not any(v in names for v in r[2:]) for r in p['source'] if r[0] not in names),'finalizer has no outward consumer')
 return names,leaves,native

def graph(p):
 known=set(p['free']);require(len(known)==len(p['free']),'unique ports')
 require(set(p['free'])==set(p['fixed_numerals'])|set(p['witnesses'])|{'x'},'exact interface')
 ct=Counter();by={}
 for r in p['source']:
  require(len(r)==4,'row arity');n,o,a,b=r
  require(type(n)is str and n not in known and o in ['+','-','*'],'unique producer')
  require(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'topological operands')
  known.add(n);by[n]=r;ct[o]+=1
 reached=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in reached:
   reached.add(v)
   if v in by:todo+=by[v][2:]
 require(known==reached,'every row and port live')
 return {'total':len(by),'M':ct['*'],'A':ct['+']+ct['-'],'witnesses':len(p['witnesses']),'free':len(p['free'])}

def univariates(rows,Q):
 env={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q:continue
  if any(type(v)is str and v not in env for v in [a,b]):continue
  aa=env[a] if type(a)is str else ({0:a} if a else {});bb=env[b] if type(b)is str else ({0:b} if b else {})
  r={}
  if o=='*':
   for i,c in aa.items():
    for j,d in bb.items():r[i+j]=r.get(i+j,0)+c*d
  else:
   r=aa.copy()
   for i,c in bb.items():r[i]=r.get(i,0)+(c if o=='+' else -c)
  env[n]={i:c for i,c in r.items() if c}
 return env

def reachable(rows,out):
 by={r[0]:r for r in rows};todo=[out];seen=set()
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in by:todo+=by[n][2:]
 return seen

def symbolic_identity(parent,child,Q,cuts):
 pool={}
 def intern(key):
  if key not in pool:pool[key]=len(pool)
  return pool[key]
 ports={n:intern(('free',n)) for n in parent['free']}
 def interpret(p):
  e=ports.copy()
  for n,o,a,b in p['source']:
   aa=e[a] if type(a)is str else intern(('integer',a));bb=e[b] if type(b)is str else intern(('integer',b))
   if n in cuts:e[n]=intern(('proved polynomial',e[Q],tuple(sorted(cuts[n].items()))))
   else:e[n]=intern(('operation',o,aa,bb))
  return e
 a=interpret(parent);b=interpret(child)
 require(a[Q]==b[Q],'same actual input-bound Q')
 require(all(a[n]==t for n,t in b.items()),'every retained register and supplied input equivalent')
 return len(child['source'])

def check(old,new,recipe,m,index):
 def w(n):return m.get(n,n)
 before=graph(old);after=graph(new)
 for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output','variant']:
  require(new[k]==old[k],'identical interface '+k)
 ob={r[0]:r for r in old['source']};nb={r[0]:r for r in new['source']}
 require(set(nb)<=set(ob),'no new producers')
 gone=set(ob)-set(nb);changes={n:nb[n] for n in nb if nb[n]!=ob[n]}
 require(len(changes)==13 and len(gone)==34,'exact actual source difference')
 require(Counter(ob[n][1] for n in gone)==Counter({'*':30,'+':4}),'deleted arithmetic count')
 actual_removed=[r for r in old['source'] if r[0] in gone]
 require(actual_removed==new['removed_rows']==recipe['removed_rows'],'literal deletion manifest')
 declared={c['new_row'][0]:c for c in new['local_identities']}
 require(set(declared)==set(changes),'local identity manifest exactly actual edits')
 require({c['new_row'][0]:c['new_row'] for c in recipe['local_identities']}==changes,'same frozen arithmetic recipe')
 Q=w('r108');require(ob[Q]==nb[Q] and ob[Q][1:3]==['*',C],'same paid Q producer')
 ou=univariates(old['source'],Q);nu=univariates(new['source'],Q)
 monomial_degrees=[];repunits=[];cuts={}
 for n,row in changes.items():
  require(row[1]=='*' and row[2] in ou and row[3] in ou,'retained paid Q-polynomial operands')
  a,b=ou[row[2]],ou[row[3]];product={}
  for i,c in a.items():
   for j,d in b.items():product[i+j]=product.get(i+j,0)+c*d
  product={k:v for k,v in product.items() if v}
  require(ou[n]==nu[n]==product,'replacement exact over Z[Q]')
  cert=declared[n]
  require(cert['old_row']==ob[n] and cert['new_row']==row,'claimed source rows')
  require(dict(cert['target_polynomial'])==product and dict(cert['left_polynomial'])==a and dict(cert['right_polynomial'])==b,'claimed expanded coefficients')
  cuts[n]=product
  if len(product)==1 and list(product.values())==[1]:monomial_degrees+=list(product)
  else:
   require(product==dict.fromkeys(range(max(product)+1),1),'repunit target');repunits.append(len(product))
 require(sorted(monomial_degrees)==[14,18,84,140,142,186,194,234,338,340,472],'all eleven power identities')
 require(sorted(repunits)==[16,98],'both repunit identities')
 provisional=[changes.get(r[0],r) for r in old['source']]
 require(reachable(provisional,old['output'])==set(nb)|set(new['free']),'deletions exactly backward dead closure')
 require([r[0] for r in old['source'] if r[0] in nb and r[0] not in ou]==[r[0] for r in new['source'] if r[0] not in ou],'all non-Q chronology unchanged')
 require(all(ou[n]==v for n,v in nu.items()),'all retained pure-Q values match')
 identities=symbolic_identity(old,new,Q,cuts)
 of,ol,on=final(old);nf,nl,nn=final(new)
 require(on==nn and ol==nl and of==nf,'same complete finalizer structure')
 require([r for r in old['source'] if r[0] in of]==[r for r in new['source'] if r[0] in nf],'all traced finalizer rows literal')
 native=[w(n) for n in BASE_NATIVE];group=[w(n) for n in BASE_GROUP]
 require(len(native)==63 and len(group)==97,'protected inventory')
 require(all(nb[n]==ob[n] for n in native+group),'all native/group/population definitions literal')
 component=new['coefficient_component'];compids={r[0] for r in old['coefficient_component']}
 require(len(component)==553 and {r[0] for r in component}==compids,'all coefficient component gates retained')
 require(component==[r for r in new['source'] if r[0] in compids] and component==recipe['coefficient_component'],'actual paid component order')
 require({n for n in compids if nb[n]!=ob[n]}=={w('cp526')},'only changed coefficient definition')
 words=[]
 for c in new['coefficient_certificates']:
  n=c['wire'];target={i:v for i,v in enumerate(c['ascending_coefficients']) if v}
  require(ou[n]==nu[n]==target,'entire coefficient word')
  words.append({'wire':n,'entries':len(c['ascending_coefficients']),'polynomial_sha256':digest(canonical(sorted(target.items())))})
 require(len(words)==4,'four outputs')
 require((after['total'],after['M'],after['A'])==(before['total']-34,before['M']-30,before['A']-4),'full recount saving')
 require(after['witnesses']==before['witnesses'],'same positive witnesses')
 for k in ['total','M','A']:require(after[k]==new['ledger'][k],'receipt ledger')
 require(new['ledger']['exact_degree']==old['ledger']['exact_degree']==[35587,53345,53347,71105][index],'degree transferred through full identity')
 require(new['degree_transfer']['parent_degree_proof_sha256']==digest(canonical(old['degree_proof'])),'degree proof object pin')
 return {'variant':new['variant'],'ledger':after,'changed_products':13,'exact_deleted_rows':34,'whole_register_identities':identities,'finalizer_rows_literal':len(nf),'residuals':len(nl),'native_literal':63,'group_population_literal':97,'coefficient_words':words,'same_entire_polynomial':True,'same_supplied_coordinates':True,'exact_degree_inherited':old['ledger']['exact_degree'],'source_sha256':digest(canonical(new['source']))}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--packet-root',type=Path,default=Path('/tmp'));ap.add_argument('--author-root',type=Path,default=Path('/tmp'));g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 for ext,h in AUTH.items():require(digest((a.author_root/('matrix193_terminal_power_composition.'+ext)).read_bytes())==h,'frozen author '+ext)
 new=load(a.author_root/'matrix193_terminal_power_composition.json');require(new['source_sha256']==AUTH['py'],'source binding')
 for n,h in new['pins'].items():
  folder=a.root if n.startswith('matrix193_entry_controller_charts.') else a.packet_root
  require(digest((folder/n).read_bytes())==h,'dependency '+n)
 require(digest((a.packet_root/'matrix193_terminal_carry_chart.json').read_bytes())==PARENT,'parent pin')
 require(digest((a.packet_root/'matrix193_cross_stage_power_reuse.json').read_bytes())==RECIPE,'recipe pin')
 old=load(a.packet_root/'matrix193_terminal_carry_chart.json');recipe=load(a.packet_root/'matrix193_cross_stage_power_reuse.json');charts=load(a.root/'matrix193_entry_controller_charts.json')
 require(len(old['packets'])==len(new['packets'])==len(recipe['packets'])==4 and len(charts['packets'])==3,'all four arrays')
 names=[r[0] for r in old['packets'][0]['source']]
 global BASE_NATIVE,BASE_GROUP
 BASE_NATIVE=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 BASE_GROUP=['r'+str(i) for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 records=[check(old['packets'][i],new['packets'][i],recipe['packets'][i],{} if i==0 else charts['packets'][i-1]['map'],i) for i in range(4)]
 answer={'review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTH,'dependency_pins':new['pins'],'packets':records,'complete_rows':sum(r['ledger']['total'] for r in records),'coefficient_entries':sum(sum(c['entries'] for c in r['coefficient_words']) for r in records),'scope':{'predecessor_execution':False,'entire_commutative_ring_identity':True,'same_positive_zero_tuples_as_immediate_parent':True,'earlier_terminal_chart_equivalence':'ordinary input only','no_new_native_or_language_proof':True}}
 if a.output:a.output.write_text(json.dumps(answer,sort_keys=True,indent=2)+'\n')
 else:require(same(answer,load(a.expect)),'independent exact receipt')
 print('PASS independent composition:6028 rows,52 product identities,16 coefficient words,all finalizers and whole outputs')
if __name__=='__main__':main()
