#!/usr/bin/env python3
"""Own standard-library emitter: authenticate and transform inert arithmetic DAG data."""
import argparse,copy,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PINS={'base':'1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95','folded':'774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91'}
def require(ok,msg):
 if not ok: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def json_bytes(o):return (json.dumps(o,indent=2,sort_keys=True)+'\n').encode()
def refs():
 for label,pin in PINS.items():
  root=ROOT/'reference'/label; b=(root/'MANIFEST.json').read_bytes();require(sha(b)==pin,'manifest pin '+label);m=json.loads(b)
  for p in sorted(root.rglob('*')):
   if not p.is_file() or p.name=='MANIFEST.json':continue
   name=str(p.relative_to(root));v=m['files'][name];b=p.read_bytes();require(sha(b)==v['sha256'] and len(b)==v['bytes'],'reference '+name)
def describe(c):
 vals={v:(1,i+2) for i,v in enumerate(c['parameters']+c['auxiliaries'])}; p=1000003;trace=[];M=A=0;constants=set();names=set(vals);anc={};
 def get(x):return (0,x%p) if type(x) is int else vals[x]
 for name,op,a,b in c['source']:
  require(name not in names and op in ['+','-','*'],'fresh/op '+name)
  for x in (a,b):require(type(x) is int or (type(x) is str and x in names),'operand '+str(x))
  names.add(name);anc[name]=[x for x in (a,b) if type(x) is str];constants.update(x for x in (a,b) if type(x) is int)
  da,ta=get(a);db,tb=get(b)
  if op=='*':d=da+db;t=ta*tb%p;M+=1
  else:
   d=max(da,db);t=((ta if da==d else 0)+(1 if op=='+' else -1)*(tb if db==d else 0))%p;A+=1
  vals[name]=(d,t);trace.append([name,d,t])
 live=set(); todo=[c['output']]
 while todo:
  q=todo.pop()
  if q in live:continue
  live.add(q);todo.extend(anc.get(q,[]))
 require(live==names,'liveness')
 d,t=vals[c['output']];require(t!=0,'degree lower bound')
 c['exact_degree_certificate']={'formal_degree':d,'gate_degree_top_trace':trace,'modulus':p,'nonzero_top_coefficient':t,'substitution_weights':{v:i+2 for i,v in enumerate(c['parameters']+c['auxiliaries'])}}
 c['ledger']={'A':A,'M':M,'SOS_gates':3*len(c['comparisons'])-1,'all_coordinates_live':True,'all_gates_live':True,'comparisons':len(c['comparisons']),'exact_degree':d,'integer_literals':sorted(constants),'natural_parameters':len(c['parameters']),'positive_witnesses':len(c['auxiliaries']),'total':M+A}
def dag_text(c):
 lines=['# Complete canonical-height clock DAG. Every +, -, * gate is paid.','# Natural ports: '+', '.join(c['parameters']),'# Strictly positive existential ports: '+', '.join(c['auxiliaries'])]
 lines += [f'{name} = {a} {op} {b}' for name,op,a,b in c['source']]
 lines += ['# Output: '+c['output']]
 return ('\n'.join(lines)+'\n').encode()
def build(old,parent_sha):
 c=copy.deepcopy(old);src=c['source'];first=next(i for i,g in enumerate(src) if g[0]=='clean_sos_res0');core=copy.deepcopy(src[:first]);require(len(src)-first==59,'old finalizer length')
 i=next(i for i,g in enumerate(core) if g[0]=='bridge_height_without_time');oldmid=core[i];oldh=core[i+1]
 require(oldmid[1]=='+' and oldmid[3]=='height_slack','old intermediate')
 require(oldh[1:]==['+','bridge_height_without_time','theta_positive'],'old height')
 require([g[0] for g in core if 'bridge_height_without_time' in g[2:]]==[oldh[0]],'single consumer')
 require(all('bridge_height_without_time' not in pair for pair in c['comparisons']),'comparison consumer')
 core[i]=['canonical_endpoint_clock_sum','+',oldmid[2],'theta_positive']
 core[i+1]=[oldh[0],'+','canonical_endpoint_clock_sum','height_slack']
 c['auxiliaries'].append('canonical_height_slack')
 c['comparisons'].append(['canonical_slack_sum','canonical_sum_plus_one'])
 core += [['canonical_slack_sum','+','height_slack','canonical_height_slack'],['canonical_sum_plus_one','+','canonical_endpoint_clock_sum',1]]
 final=[]
 for j,(a,b) in enumerate(c['comparisons']):final += [[f'clean_sos_res{j}','-',a,b],[f'clean_sos_sq{j}','*',f'clean_sos_res{j}',f'clean_sos_res{j}']]
 last='clean_sos_sq0'
 for j in range(1,len(c['comparisons'])):
  name=f'clean_sos_sum{j}';final.append([name,'+',last,f'clean_sos_sq{j}']);last=name
 c['source']=core+final;c['output']=last
 c['format']='complete-unbounded-clean-clock-canonical-height-v1'
 c['model']=old['model'].replace('-literal-folded','-canonical-height')
 c['all_tuple_identity']='New complete output = folded parent output + (height_slack + canonical_height_slack - (bridge_input + bridge_target + theta_positive) - 1)^2, over all integer tuples.'
 c['canonical_height']={'added_positive_coordinate':'canonical_height_slack','h_register':oldh[0],'S_register':'canonical_endpoint_clock_sum','constraint':'eta+kappa=S+1','meaning_on_positive_zeros':'h is the unique dyadic integer with S<h<=2S; the least power of two strictly above S','reassociation_original':[oldmid,oldh],'reassociation_new':core[i:i+2],'parent_sha256':parent_sha,'folded_manifest_sha256':PINS['folded'],'native_positive_coordinate_count':22,'outer_fiber_statement':'Every accepted nonempty fiber projects bijectively onto the retained complete 22-coordinate positive native AND-extension fiber at fixed padded ports and fixed prescribed scale. Native multiplicity is unresolved.'}
 c['scope']='Eligible fixed source and nonempty first halt, integer domains only. Canonical outer height; no full unique/finite witness claim, ordinary-input universal loader, or native Pell materialization.'
 describe(c);return c
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');opts=a.parse_args();refs();products={};rows={}
 for p in sorted((ROOT/'reference/folded/circuits').glob('*.json')):
  c=build(json.loads(p.read_bytes()),sha(p.read_bytes()));name=p.stem.replace('-folded','-canonical');products['circuits/'+name+'.json']=json_bytes(c);products['circuits/'+name+'.dag.txt']=dag_text(c);rows[name]=c['ledger']
 for p in sorted((ROOT/'reference/base/circuits').glob('zero-step-*.json')):
  products['circuits/'+p.name]=p.read_bytes();c=json.loads(p.read_bytes());rows[p.stem]=c['ledger']
 receipt={'format':'canonical-height-emission-v1','frozen_manifest_pins':PINS,'circuits':rows,'files':{k:{'sha256':sha(v),'bytes':len(v)} for k,v in sorted(products.items())}}
 products['receipts/emission.json']=json_bytes(receipt)
 for name,b in products.items():
  p=ROOT/name
  if opts.check:require(p.read_bytes()==b,'emission mismatch '+name)
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'status':'PASS','mode':'read-only replay' if opts.check else 'emitted','circuits':rows},sort_keys=True))
if __name__=='__main__':main()
