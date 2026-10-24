#!/usr/bin/env python3
"""Build a102-gate, degree368 positive weighted-root sibling."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-shifted-strong'
OUT=ROOT/'candidates/ten-positive-weighted-roots'
PARENT_SHA='7800654c08a096342c72e7f18a14d7362ebe1a0ab29aa19a3ebbcfa41e73fc0f'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'whole frozen102/388 parent')
 parent=json.loads(raw);old=parent['source']
 need(old[41:43]==[['shift_i','+','i','q2'],['I','*','shift_i','c2']]and old[84]==['fa','*','dM2','Dtau'],'exact strong and root cuts')
 rows=[];records=[];insertions=[]
 for i,row in enumerate(old):
  if i==41:
   records.append(dict(parent_index=i,status='deleted_private',old_row=row));continue
  if i==84:
   inserted=['Dtau9','*',9,'Dtau'];insertions.append(dict(child_index=len(rows),row=inserted));rows.append(inserted)
  changed={42:['I','*','i','c2'],84:['fa','*','dM2','Dtau9']}
  new=deepcopy(changed.get(i,row));records.append(dict(parent_index=i,child_index=len(rows),old_row=row,new_row=new,
    status='replaced_cut'if i in changed else'retained'));rows.append(new)
 child=deepcopy(parent);counts=dict(Counter(row[1]for row in rows));need(counts=={'*':60,'+':24,'-':18},'actual102 operation inventory')
 degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
 child.update(name='ten_positive_weighted_tau_degree368',source=rows,operations=102,
  operation_breakdown=counts,exact_degree=368,syntactic_degree=degrees['N'],
  register_degrees={k:degrees[k]for k in parent['register_degrees']},parent_sha256=PARENT_SHA,
  proof='PROOF.md',proof_status='Ordinary positivezero/refutation equivalence via modulus-mu noncancellation of(3tau,f,y), I=ic², restored postextraction transport and explicit canonicalpositive maps. No newLean/internal-ZFC proof.')
 files={'equation.json':encoded(child),'source/weighted-parent-equation.json':raw,
  'source/SHIFTED_PROOF.md':(PARENT/'PROOF.md').read_bytes(),
  'source/weighted-parent-check.json':(PARENT/'CHECK.json').read_bytes(),
  'source/weighted-parent-check-optimized.json':(PARENT/'CHECK_OPTIMIZED.json').read_bytes()}
 deps={
  'source/weighted-parent-equation.json':PARENT/'equation.json',
  'source/SHIFTED_PROOF.md':PARENT/'PROOF.md',
  'source/weighted-parent-check.json':PARENT/'CHECK.json',
  'source/weighted-parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json'}
 for p in(PARENT/'source').rglob('*'):
  if p.is_file():name=str(p.relative_to(PARENT));files[name]=p.read_bytes();deps[name]=p
 for name,pin in json.loads((PARENT/'PROVENANCE.json').read_bytes())['dependencies'].items():deps[name]=ROOT/pin['repository_path']
 # The final packet requires its exact independently reviewed ordinary proof.
 for suffix in('md','json'):
  p=ROOT/('reviews/ten-positive-weighted-roots-ordinary-peer.'+suffix)
  name='source/WEIGHTED_ORDINARY_PEER.'+suffix;files[name]=p.read_bytes();deps[name]=p
 files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
 for pin in parent['coefficient_binding']['ports'].values():
  name='coefficients/'+pin['file'];files[name]=(PARENT/name).read_bytes()
 files['CUTS.json']=encoded(dict(parent_sha256=PARENT_SHA,all_parent_rows=records,inserted_rows=insertions,
  changed_parent_indices=[42,84],deleted_parent_indices=[41],child_norm_tail_start=89,parent_norm_tail_start=89,
  kernel_polynomial_map='i_child=i_parent+q²; all other inputs unchanged; full kernel/carrier match, fa_child=9fa_parent',
  canonical_positive_map='i_child=i_parent+q²; n_child=n_parent+2tau, where the canonicalparentcenter=tau+f+y',
  boundary='No pointwiseoutputidentity or positiveinversei_parent=i_child-q² isclaimed. Fullzeroexistence equivalence uses PROOF.md.'))
 files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
  generator_sha256=digest(Path(__file__).read_bytes()),
  dependencies={n:dict(repository_path=str(p.relative_to(ROOT)),sha256=digest(files[n]))for n,p in deps.items()},
  coefficient_family='whole originalcompact44; wholeBFS page specialization licensed separately by uniformnative/source theorem',
  canonical_page_unchanged=True,boundary='Ordinary unboundedproof, no newLean or encodedobject-ZFC derivation.'))
 files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=102,operation_breakdown=counts,
  exact_degree=368,syntactic_degree=degrees['N'],sha256={n:digest(data)for n,data in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
 for name,data in build().items():
  path=OUT/name
  if a.check:need(path.read_bytes()==data,'byte-identical '+name)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
 print(json.dumps(dict(status='PASS',check=a.check,positive_variables=10,operations=102,exact_degree=368),indent=2))
if __name__=='__main__':main()
