#!/usr/bin/env python3
"""Build the102-gate positive shifted-strong/short-transport sibling."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-free-j'
OUT=ROOT/'candidates/ten-positive-shifted-strong'
PARENT_SHA='1b20a25bddd6c494222c19d74142b53960f18b39be9fe323b49a4e5667e4d318'

def need(ok,message):
 if not ok:raise ValueError(message)
def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'complete frozen freeJ103 parent')
 parent=json.loads(raw);old=parent['source'];changes={
 41:['shift_i','+','i','q2'],42:['I','*','shift_i','c2'],
 56:['HI','*','Hp','I'],58:['L','+','HI','cTR']}
 need(old[41:43]==[['muc2','*','mu','c2'],['I','*','i','muc2']]and
      old[56:59]==[['4Am1I','*','4Am1','I'],['L1','+','cTR','cT'],['L','+','4Am1I','L1']],
      'complete strong and transport cuts')
 rows=[];records=[]
 for i,row in enumerate(old):
  if i==57:records.append(dict(parent_index=i,status='deleted_private',old_row=row));continue
  nr=deepcopy(changes.get(i,row));records.append(dict(parent_index=i,child_index=len(rows),
    status='replaced_cut'if i in changes else'retained',old_row=row,new_row=nr));rows.append(nr)
 child=deepcopy(parent);counts=dict(Counter(r[1]for r in rows));need(counts=={'*':59,'+':25,'-':18},'102-gate census')
 degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
 child.update(name='ten_positive_shifted_strong_degree388',source=rows,operations=102,
  operation_breakdown=counts,exact_degree=388,syntactic_degree=degrees['N'],
  register_degrees={k:degrees[k]for k in parent['register_degrees']},parent_sha256=PARENT_SHA,
  proof_status='Ordinary positive-zero/refutation equivalence via shiftedstronglowerbound and shorterpositive transport; exact polynomial inputmap plusfreshcanonicaln. No newLean/internal-ZFC proof.')
 files={'equation.json':encoded(child),'source/shift-parent-equation.json':raw,
  'source/FREE_J_PROOF.md':(PARENT/'PROOF.md').read_bytes(),
  'source/shift-parent-check.json':(PARENT/'CHECK.json').read_bytes(),
  'source/shift-parent-check-optimized.json':(PARENT/'CHECK_OPTIMIZED.json').read_bytes(),
  'source/parent-checker-helpers.py':(PARENT/'check.py').read_bytes()}
 deps={
  'source/shift-parent-equation.json':PARENT/'equation.json',
  'source/FREE_J_PROOF.md':PARENT/'PROOF.md',
  'source/shift-parent-check.json':PARENT/'CHECK.json',
  'source/shift-parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json',
  'source/parent-checker-helpers.py':PARENT/'check.py',
 }
 for p in(PARENT/'source').rglob('*'):
  if p.is_file():
   name=str(p.relative_to(PARENT));files[name]=p.read_bytes();deps[name]=p
 inherited=json.loads((PARENT/'PROVENANCE.json').read_bytes())['dependencies']
 for name,pin in inherited.items():deps[name]=ROOT/pin['repository_path']
 for suffix in('md','json'):
  name='source/SHIFTED_ORDINARY_PEER.'+suffix
  deps[name]=ROOT/('reviews/ten-positive-shifted-strong-ordinary-peer.'+suffix)
  files[name]=deps[name].read_bytes()
 files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
 for pin in parent['coefficient_binding']['ports'].values():
  name='coefficients/'+pin['file'];files[name]=(PARENT/name).read_bytes()
 files['CUTS.json']=encoded(dict(parent_sha256=PARENT_SHA,all_parent_rows=records,
  changed_parent_indices=sorted(changes),deleted_parent_indices=[57],
  strong_identity='I_child(i_child=mu*i_parent-q²)=I_parent',
  positive_i_map='i_child=mu*(i_parent-1)+1>=1',
  transport_identity='L_child=L_parent-I-cT; W_child=W_parent-(q-1)(I+cT)',
  universal_full_polynomial_map='i_child=mu*i_parent-q²; n_child=n_parent-(I_parent+cT)*Bt; allotherinputsunchanged',
  positivity_boundary='The nmap is notclaimedpositiveforarbitraryparentassignments. Canonicalcompletenessreconstructsnfrompositive rootsasPROOF.md states.',
  child_norm_tail_start=89))
 files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
  generator_sha256=digest(Path(__file__).read_bytes()),
  dependencies={name:dict(repository_path=str(path.relative_to(ROOT)),sha256=digest(files[name]))for name,path in deps.items()},
  coefficient_family='whole original compact44; separately calibratedBFS satisfies samearithmeticbox',
  canonical_page_unchanged=True,formalization_boundary='No newLean or encoded object-ZFC proof; ordinarynative/refutationcalibration retained.'))
 files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=102,
  operation_breakdown=counts,exact_degree=388,syntactic_degree=degrees['N'],
  sha256={n:digest(raw)for n,raw in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
 for name,raw in build().items():
  path=OUT/name
  if a.check:need(path.read_bytes()==raw,'byte-identical '+name)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
 print(json.dumps(dict(status='PASS',check=a.check,positive_variables=10,operations=102,exact_degree=388),indent=2))
if __name__=='__main__':main()
