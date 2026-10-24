#!/usr/bin/env python3
"""Build a101-operation positive short-projection sibling of degree368."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-weighted-roots'
OUT=ROOT/'candidates/ten-positive-short-projection'
PARENT_SHA='dea8cdd2489b6797188335f0984cb8ac423f316d22966a149ab592f0cb91e192'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'complete frozen102/368 parent')
 parent=json.loads(raw);old=parent['source']
 need(old[18]==['ap','-','Am1',1]and old[64:70]==[
  ['apc','*','ap','c'],['2apc','*',2,'apc'],['X2apc','+','X','2apc'],
  ['Kquad0','*','X','X2apc'],['Kquad','-','Kquad0',1],['lin','+','Hn','Kquad']], 'exact private/projection/carrier cuts')
 changes={64:['threec','*',3,'c'],65:['twoX','*',2,'X'],66:['gap','-','threec','twoX'],
  67:['Kpos0','*','X','gap'],68:['Kpos','+','Kpos0',2],69:['lin','+','Hn','Kpos']}
 rows=[];records=[]
 for i,row in enumerate(old):
  if i==18:records.append(dict(parent_index=i,status='deleted_private',old_row=row));continue
  new=deepcopy(changes.get(i,row));records.append(dict(parent_index=i,child_index=len(rows),old_row=row,new_row=new,
    status='replaced_cut'if i in changes else'retained'));rows.append(new)
 child=deepcopy(parent);counts=dict(Counter(row[1]for row in rows));need(counts=={'*':60,'+':24,'-':17},'actual101 operation count')
 degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
 register_degrees={k:degrees[k]for k in parent['register_degrees']if k!='Kquad'};register_degrees['Kpos']=degrees['Kpos']
 child.update(name='ten_positive_short_positive_projection_degree368',source=rows,operations=101,
  operation_breakdown=counts,exact_degree=368,syntactic_degree=degrees['N'],register_degrees=register_degrees,
  parent_sha256=PARENT_SHA,proof='PROOF.md',proof_status='Ordinary positivezero/refutation equivalence using Kpos=HXc-2Kquad, oddH whole-product license and strictpositiven map. No newLean/internal-ZFC proof.')
 files={'equation.json':encoded(child),'source/projection-parent-equation.json':raw,
  'source/WEIGHTED_PROOF.md':(PARENT/'PROOF.md').read_bytes(),
  'source/projection-parent-check.json':(PARENT/'CHECK.json').read_bytes(),
  'source/projection-parent-check-optimized.json':(PARENT/'CHECK_OPTIMIZED.json').read_bytes()}
 deps={
  'source/projection-parent-equation.json':PARENT/'equation.json',
  'source/WEIGHTED_PROOF.md':PARENT/'PROOF.md',
  'source/projection-parent-check.json':PARENT/'CHECK.json',
  'source/projection-parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json'}
 for p in(PARENT/'source').rglob('*'):
  if p.is_file():name=str(p.relative_to(PARENT));files[name]=p.read_bytes();deps[name]=p
 for name,pin in json.loads((PARENT/'PROVENANCE.json').read_bytes())['dependencies'].items():deps[name]=ROOT/pin['repository_path']
 for suffix in('md','json'):
  p=ROOT/('reviews/ten-positive-short-projection-ordinary-peer.'+suffix)
  name='source/SHORT_ORDINARY_PEER.'+suffix;files[name]=p.read_bytes();deps[name]=p
 files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
 for pin in parent['coefficient_binding']['ports'].values():
  name='coefficients/'+pin['file'];files[name]=(PARENT/name).read_bytes()
 files['CUTS.json']=encoded(dict(parent_sha256=PARENT_SHA,all_parent_rows=records,
  changed_parent_indices=sorted(changes),deleted_parent_indices=[18],parent_norm_tail_start=89,child_norm_tail_start=88,
  projection_identity='Kpos=H*X*c-2*Kquad',
  positive_map='n_child=n_parent+3*kappa-X*c, whereH*kappa=Kquad; allotherinputsunchanged',
  universal_center_cut='H*(n+3u-X*c)+Kpos-(H*n+Kquad)=3*(H*u-Kquad)',
  boundary='No positivepointwiseinverse or unconditionalquotientinputmap isclaimed; fullsoundness usesretained sourceandkernelproof.'))
 files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,generator_sha256=digest(Path(__file__).read_bytes()),
  dependencies={n:dict(repository_path=str(p.relative_to(ROOT)),sha256=digest(files[n]))for n,p in deps.items()},
  coefficient_family='whole authenticoriginalcompact44; wholeBFS page separately licensed byuniformnative/sourceproof',
  canonical_page_unchanged=True,boundary='Ordinary unboundedproof; no newLean or encodedobject-ZFC derivation.'))
 files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=101,operation_breakdown=counts,
  exact_degree=368,syntactic_degree=degrees['N'],sha256={n:digest(data)for n,data in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
 for name,data in build().items():
  path=OUT/name
  if a.check:need(path.read_bytes()==data,'byte-identical '+name)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
 print(json.dumps(dict(status='PASS',check=a.check,positive_variables=10,operations=101,exact_degree=368),indent=2))
if __name__=='__main__':main()
