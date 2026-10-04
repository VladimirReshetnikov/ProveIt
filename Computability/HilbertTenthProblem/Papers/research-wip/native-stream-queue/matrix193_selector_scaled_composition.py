#!/usr/bin/env python3
"""Fresh complete composition of shared selector blocks and a paid scaled power."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
PINS={'matrix193_selector_block_sharing.py': '25a3416d94475f1df98aa34f20a9e182e4ea6fcc2e39ff6b47c401eadd40790a', 'matrix193_selector_block_sharing.json': 'cfaab226e28465ee1332bd38915ca49e6befe91a2931181d19eaf66603121584', 'matrix193_selector_block_sharing.md': '0f42494cede122d0373fb1fb8c249ea612d480e13fa651f7ece4daff76e42cd9', 'matrix193_scaled_power_reuse.py': '2186513567e31204f78726d856686be2818205638563e9b1cfa052b382177942', 'matrix193_scaled_power_reuse.json': 'c81bb0ef774361b1b8b4f1b6084ec90329f9c0e22665d8968ced5517959de2b4', 'matrix193_scaled_power_reuse.md': '39114f292022ef9bd6dbd5065eed34c5634b77e4050556faa69ae2f656d466b8', 'matrix193_entry_controller_charts.py': '7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf', 'matrix193_entry_controller_charts.json': 'd5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571', 'matrix193_entry_controller_charts.md': '27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122'}
def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def encoded(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load(p):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(v):raise ValueError('nonfinite JSON '+v)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b) and all(same(x,y)for x,y in zip(a,b))
 return a==b
def poly(rows,Q):
 e={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q or any(type(v)is str and v not in e for v in (a,b)):continue
  av=e[a]if type(a)is str else {0:a};bv=e[b]if type(b)is str else {0:b}
  r={}
  if o=='*':
   for i,c in av.items():
    for j,d in bv.items():r[i+j]=r.get(i+j,0)+c*d
  else:
   r=av.copy()
   for i,c in bv.items():r[i]=r.get(i,0)+(c if o=='+'else-c)
  e[n]={i:c for i,c in r.items()if c}
 return e
def reorder(rows,output):
 by={r[0]:r for r in rows};live=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:
   live.add(n)
   if n in by:todo+=by[n][2:]
 active=set();done=set();out=[]
 def emit(n):
  if type(n)is int or n not in by or n in done:return
  need(n not in active,'acyclic dependency graph');active.add(n)
  for v in by[n][2:]:emit(v)
  active.remove(n);done.add(n);out.append(by[n])
 for r in rows:
  if r[0]in live:emit(r[0])
 return out,live
def audit(p):
 known=set(p['free']);need(len(known)==len(p['free']),'unique ports')
 need(known=={'x'}|set(p['witnesses'])|set(p['fixed_numerals']),'exact free interface')
 d={n:0 if n in p['fixed_numerals']else 1 for n in known};count=Counter()
 for n,o,a,b in p['source']:
  need(type(n)is str and n not in known and o in ('*','+','-'),'unique producer')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'paid prior operands')
  da,db=(d[v]if type(v)is str else 0 for v in (a,b));d[n]=da+db if o=='*'else max(da,db)
  known.add(n);count[o]+=1
 _,live=reorder(p['source'],p['output']);need(live==known,'all rows and ports live')
 return {'total':len(p['source']),'M':count['*'],'A':count['+']+count['-'],'positive_witnesses':len(p['witnesses']),
  'supplied_ports':len(p['free']),'fixed_coefficient_ports':len(p['fixed_numerals']),
  'integer_literals':len({v for r in p['source']for v in r[2:]if type(v)is int}),
  'syntactic_degree_upper':d[p['output']],'all_live':True}
def finalizer(p,N):
 by={r[0]:r for r in p['source']};out=by[p['output']];need(out[1]=='-'and out[3]==1,'final minus one')
 prod=by[out[2]];need(prod[1:3]==['*',N],'final native product');one=by[prod[3]];need(one[1]=='+'and one[3]==1,'one plus SOS')
 names={out[0],prod[0],one[0]};leaves=[]
 def walk(n):
  r=by[n];names.add(n)
  if r[1]=='*':
   need(r[2]==r[3]and type(r[2])is str,'square leaf');names.add(r[2]);leaves.append(r[2]);return
  need(r[1]=='+','sum tree');walk(r[2]);walk(r[3])
 walk(one[2]);need(leaves==p['retained_residual_wires']and len(set(leaves))==len(leaves),'every residual once')
 need(len(names)==3*len(leaves)+2,'complete finalizer size')
 need(all(not any(v in names for v in r[2:])for r in p['source']if r[0]not in names),'private finalizer')
 return [r for r in p['source']if r[0]in names]
def whole_identity(old,new,Q,target):
 pool={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 inputs={n:intern(('port',n))for n in old['free']}
 def run(rows):
  e=inputs.copy()
  for n,o,a,b in rows:
   aa,bb=(e[v]if type(v)is str else intern(('literal',v))for v in (a,b))
   e[n]=intern(('proved polynomial',e[Q],162,-20))if n==target else intern((o,aa,bb))
  return e
 a,b=run(old['source']),run(new['source']);need(a[Q]==b[Q],'same actual Q expression')
 need(all(a[n]==v for n,v in b.items()),'every retained register and full output equal')
 return len(new['source'])
def transform(old,recipe,m,index,native,groups):
 def w(n):return m.get(n,n)
 oldby={r[0]:r for r in old['source']};Q=w('r108');target=w('cp345');removed=w('cp344')
 need(oldby[target]==[target,'*',-20,removed],'old target')
 need(oldby[removed]==[removed,'*',w('r138'),w('r200')],'private Q162 producer')
 newrow=[target,'*',w('cp317'),w('cp400')]
 need(old['variant']==recipe['variant'],'variant correspondence')
 need(recipe['identity']['old_target']==oldby[target] and recipe['identity']['new_target']==newrow and recipe['identity']['deleted_row']==oldby[removed],'exact authenticated scaled branch recipe')
 before=poly(old['source'],Q)
 need(before[removed]=={162:1}and before[target]=={162:-20},'old target polynomial')
 need(before[w('cp317')]=={150:1}and before[w('cp400')]=={12:-20},'paid replacement operands')
 need(oldby[w('cp400')]==[w('cp400'),'*',-2,w('cp333')],'actual paid negative multiple')
 provisional=[newrow if r[0]==target else r for r in old['source']];rows,live=reorder(provisional,old['output'])
 need([r[0]for r in old['source']if r[0]not in live]==[removed],'exact one dead producer')
 new={k:old[k]for k in ('variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires')};new['source']=rows
 by={r[0]:r for r in rows};need(all(r==newrow if n==target else r==oldby[n]for n,r in by.items()),'every other retained definition literal')
 after=poly(rows,Q);need(all(before[n]==v for n,v in after.items()),'all retained Q-polynomials equal')
 need(after[target]=={162:-20},'rescheduled target polynomial')
 need([r[0]for r in old['source']if r[0]in by and r[0]not in before]==[r[0]for r in rows if r[0]not in before],'non-Q order unchanged')
 ids={r[0]for r in old['coefficient_component']};component=[r for r in rows if r[0]in ids]
 need(set(by)&ids==ids-{removed}and len(component)==552,'complete coefficient component')
 count=Counter(r[1]for r in component);need((count['*'],count['+']+count['-'])==(304,248),'component counts')
 need(component==recipe['coefficient_component'],'complete552 component agrees with scaled branch')
 new['coefficient_component']=component;new['component_ledger']={'total':552,'M':304,'A':248}
 selector=old['shared_selector_component'];need(len(selector)==242 and all(by[r[0]]==r for r in selector),'all242 shared selector rows literal')
 need([r for r in rows if r[0]in {a[0]for a in selector}]==selector,'shared selector execution order literal')
 new['shared_selector_component']=selector;new['selector_ledger']={'total':242,'M':121,'A':121}
 new['selector_words']=old['selector_words']
 for c in old['coefficient_certificates']:need(after[c['wire']]=={i:v for i,v in enumerate(c['ascending_coefficients'])if v},'entire coefficient word')
 new['coefficient_certificates']=old['coefficient_certificates']
 need(all(by[w(n)]==oldby[w(n)]for n in native+groups),'all native and grouped population definitions literal')
 oldfinal,newfinal=finalizer(old,w('eight_units')),finalizer(new,w('eight_units'));need(oldfinal==newfinal,'entire traced finalizer literal')
 ledger=audit(new);prior=audit(old)
 need((ledger['total'],ledger['M'],ledger['A'])==(prior['total']-1,prior['M']-1,prior['A']),'complete saving')
 ledger['exact_degree']=old['ledger']['exact_degree'];ledger['outer_residuals']=len(new['retained_residual_wires']);new['ledger']=ledger
 new['identity']={'retained_registers_compared':whole_identity(old,new,Q,target),'same_complete_polynomial':True,'actual_Q_bound':True,'old_target':oldby[target],'new_target':newrow,'deleted_row':oldby[removed],'target_polynomial':[[162,-20]],'left_polynomial':[[150,1]],'right_polynomial':[[12,-20]]}
 new['boundaries']={'shared_selector_rows_literal':242,'native_rows_literal':len(native),'group_population_rows_literal':len(groups),'finalizer_rows_literal':len(newfinal),'all_other_retained_definitions_literal':True}
 new['parent_reference']={'receipt':'matrix193_selector_block_sharing.json','packet_index':index,'source_sha256':sha(encoded(old['source'])),'degree_transfer_sha256':sha(encoded(old['degree_transfer'])),'exact_degree_inherited_by_full_identity':True}
 new['scaled_recipe_reference']={'receipt':'matrix193_scaled_power_reuse.json','packet_index':index,'source_sha256':sha(encoded(recipe['source']))}
 return new
def build(root,packet_root):
 for n,h in PINS.items():
  directory=root if n.startswith('matrix193_entry_controller_charts.')else packet_root
  need(sha((directory/n).read_bytes())==h,'frozen dependency '+n)
 parent=load(packet_root/'matrix193_selector_block_sharing.json');recipe=load(packet_root/'matrix193_scaled_power_reuse.json');maps=load(root/'matrix193_entry_controller_charts.json')
 for name,data in [('matrix193_selector_block_sharing',parent),('matrix193_scaled_power_reuse',recipe),('matrix193_entry_controller_charts',maps)]:
  need(data['source_sha256']==PINS[name+'.py'],'source binding')
 need(len(parent['packets'])==len(recipe['packets'])==4 and len(maps['packets'])==3,'complete four-variant inventory')
 names=[r[0]for r in parent['packets'][0]['source']];native=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 groups=['r'+str(i)for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 need(len(native)==63 and len(groups)==97,'protected inventory')
 packets=[transform(p,recipe['packets'][i],{}if i==0 else maps['packets'][i-1]['map'],i,native,groups)for i,p in enumerate(parent['packets'])]
 need([p['ledger']['total']for p in packets]==[1417,1414,1414,1411],'complete counts')
 need([p['ledger']['positive_witnesses']for p in packets]==[141,140,140,139],'unchanged witness counts')
 need([p['ledger']['exact_degree']for p in packets]==[35587,53345,53347,71105],'inherited exact degrees')
 return {'schema':'matrix193-selector-scaled-composition-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,
  'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source'])for p in packets),'complete_coefficient_words':16,'coefficient_entries':sum(len(c['ascending_coefficients'])for p in packets for c in p['coefficient_certificates']),'full_ring_identities':4,'explicit_finalizer_traces':8,'literal_selector_components':4},
  'scope':{'frozen_code_executed_or_imported':False,'same_supplied_coordinates_and_polynomial_as_immediate_selector_parent':True,'same_positive_zero_tuples_as_immediate_parent':True,'exact_degrees_inherited':True,'older_terminal_and_IDLE_comparisons':'ordinary input only','new_native_or_trajectory_fixture':False,'no_minimality_claim':True,'universal84_unchanged':True}}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--packet-root',type=Path);g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=a.parse_args();result=build(args.root,args.packet_root or args.root)
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:need(same(result,load(args.expect)),'type-exact frozen receipt')
 print('PASS full1417/1414/1414/1411;552 coefficient and242 selector rows;four entire polynomial identities')
if __name__=='__main__':main()
