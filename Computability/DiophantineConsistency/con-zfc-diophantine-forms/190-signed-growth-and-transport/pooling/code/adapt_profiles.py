#!/usr/bin/env python3
"""Research helper: transfer checked acyclic pivots by named source rows."""
import json, pathlib, importlib.util, hashlib, copy
ROOT=pathlib.Path(__file__).resolve().parent.parent
OLD=ROOT.parents[1]/'sources/incoming_unpacked/ConZFC_Signed_Horizons_and_Residue_Carriers_2026-10-25/ConZFC_Signed_Horizons_and_Residue_Carriers_2026-10-25/direct'
def load(p):return json.loads(p.read_bytes())
def module(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
proj=module('projection',ROOT/'inherited/build_projections_original.py')
def units(row):
 p={tuple(m):c for c,m in row['terms']}
 return [m[0] for m,c in p.items() if len(m)==1 and abs(c)==1 and all(m[0] not in t for t in p if t!=m)]
def named(row,variables):
 return tuple(sorted((tuple(sorted(variables[i]['name'] for i in mon)),c) for c,mon in row['terms']))
def adapt(name,variant):
 pc=load(OLD/'certificates'/name);old=load(OLD/'sources'/pc['anchor']/pc['variant']/'equation.json')
 new=load(ROOT/'sources'/variant/'equation.json');pool=load(ROOT/'sources'/variant/'certificate.json')
 names={v['name']:i for i,v in enumerate(new['variables'])};steps=[];used=set()
 logs=[]
 for st in pc['steps']:
  oldv=old['variables'][st['variable']]['name'];ro=old['residuals'][st['row']]
  if oldv not in names:logs.append({'old':st,'name':oldv,'status':'absent'});continue
  v=names[oldv];candidates=[i for i,r in enumerate(new['residuals']) if i not in used and v in units(r)]
  exact=[i for i in candidates if named(new['residuals'][i],new['variables'])==named(ro,old['variables'])]
  label=[i for i in candidates if new['residuals'][i]['label']==ro['label']]
  if len(exact)==1:r=exact[0]
  elif len(label)==1:r=label[0]
  elif len(candidates)==1:r=candidates[0]
  else:
   logs.append({'old':st,'name':oldv,'status':'ambiguous','candidates':candidates});continue
  steps.append({'row':r,'variable':v});used.add(r)
 profile={'schema':'acyclic-unit-projection-v1','variant':variant,'steps':steps,'variables':len(new['variables'])-len(steps),'degree_bound':pc['degree_bound'],'adapted_from':name}
 raw=(ROOT/'sources'/variant/'equation.json').read_bytes()
 try:
  out=proj.build(new,pool,profile,hashlib.sha256(raw).hexdigest());print(name,variant,out['metrics'])
 except (ValueError,KeyError) as ex:
  print(name,variant,'ERROR',str(ex));return
 dest=ROOT/'search';dest.mkdir(exist_ok=True);(dest/(name+'_'+variant)).write_text(json.dumps({'profile':profile,'logs':logs,'metrics':out['metrics']},indent=2))
if __name__=='__main__':
 for name in ['integer131_degree12_paired.json','integer117_degree16_paired.json','integer108_degree32_staged.json','integer97_degree128_all5.json','integer91_degree256_all5.json','integer87_degree32768_all5.json','integer86_degree2097780_all5.json']:
  for variant in ['staged','all4','separate']:adapt(name,variant)
