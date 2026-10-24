#!/usr/bin/env python3
"""Build the ten-positive107-operation direct-base endpoint of degree340."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-short-projection'
OUT=ROOT/'candidates/ten-positive-direct-base'
PARENT_SHA='cf2748fc277a20a419f196d28674e5374316d5f29fae5ef49c7b113e13b19edd'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'wholefrozen101/368 parent');parent=json.loads(raw)
 need(parent['source'][4]==['X','*','w','q']and parent['source'][38]==['Bt','-','K0wC','F']and parent['source'][73]==['inner','-','qm1Y','q3WBt'],'all primitivebase/carrier cuts')
 changes={4:['X','+','q','x'],36:['qK0X','+','qK0','X'],37:['qK0XC','*','qK0X','C'],38:['B','-','qK0XC','qF'],
  56:['qm1L','*','qbJ','L'],58:['P1','*','q4','bJ'],70:['lowY','*','qbJ','Y'],71:['WBt','*','W','B'],73:['inner0','-','lowY','q3WBt']}
 before={36:[['qK0','*','q','K0']],38:[['qF','*','q','F']],56:[['qbJ','*','q','bJ']],58:[['q4','*','q3','q']],73:[['lowX','*','bJ','X']]}
 after={73:[['inner','-','inner0','lowX']]};rows=[];records=[];insertions=[]
 for j,old in enumerate(parent['source']):
  for row in before.get(j,[]):insertions.append(dict(parent_index=j,position='before',child_index=len(rows),row=row));rows.append(row)
  new=deepcopy(changes.get(j,old));records.append(dict(parent_index=j,child_index=len(rows),old_row=old,new_row=new,status='replaced_cut'if j in changes else'retained'));rows.append(new)
  for row in after.get(j,[]):insertions.append(dict(parent_index=j,position='after',child_index=len(rows),row=row));rows.append(row)
 child=deepcopy(parent);child.update(witnesses=['x'if v=='w'else v for v in parent['witnesses']])
 counts=dict(Counter(r[1]for r in rows));need(len(rows)==107 and counts=={'*':64,'+':25,'-':18},'actual107 operations')
 degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  da,db=(0 if type(v)is int else degrees[v]for v in(a,b));degrees[n]=da+db if o=='*'else max(da,db)
 child.update(name='ten_positive_direct_base_degree340',source=rows,operations=107,operation_breakdown=counts,exact_degree=340,syntactic_degree=degrees['N'],
  register_degrees={n:degrees[n]for n in parent['register_degrees']},parent_sha256=PARENT_SHA,proof='PROOF.md',
  proof_status='Ordinary positivezero/refutationequivalence viaq^-4carrier, delayedqdivX andpositiveW/nwitnessmap. No newLean/internal-ZFC derivation.')
 files={'equation.json':encoded(child),'source/direct-parent-equation.json':raw,'source/SHORT_PROOF.md':(PARENT/'PROOF.md').read_bytes(),
  'source/direct-parent-check.json':(PARENT/'CHECK.json').read_bytes(),'source/direct-parent-check-optimized.json':(PARENT/'CHECK_OPTIMIZED.json').read_bytes()}
 deps={'source/direct-parent-equation.json':PARENT/'equation.json','source/SHORT_PROOF.md':PARENT/'PROOF.md',
  'source/direct-parent-check.json':PARENT/'CHECK.json','source/direct-parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json'}
 for p in(PARENT/'source').rglob('*'):
  if p.is_file():n=str(p.relative_to(PARENT));files[n]=p.read_bytes();deps[n]=p
 for n,pin in json.loads((PARENT/'PROVENANCE.json').read_bytes())['dependencies'].items():deps[n]=ROOT/pin['repository_path']
 for suffix in('md','json'):
  p=ROOT/('reviews/ten-positive-direct-base-ordinary-peer.'+suffix)
  n='source/DIRECT_ORDINARY_PEER.'+suffix;files[n]=p.read_bytes();deps[n]=p
 for n,p in {
  'source/DIRECT_PEER_SCRIPT.py':ROOT/'reviews/ten-positive-direct-base-ordinary-peer.py',
  'source/DIRECT_PEER_OPTIMIZED.json':ROOT/'reviews/ten-positive-direct-base-ordinary-peer_OPTIMIZED.json',
 }.items():files[n]=p.read_bytes();deps[n]=p
 files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
 for pin in parent['coefficient_binding']['ports'].values():
  n='coefficients/'+pin['file'];files[n]=(PARENT/n).read_bytes()
 files['CUTS.json']=encoded(dict(parent_sha256=PARENT_SHA,all_parent_rows=records,inserted_rows=insertions,changed_parent_indices=sorted(changes),
  parent_input='w',child_input='x',parent_norm_tail_start=88,child_norm_tail_start=94,
  positive_map='x=Xold-q;n_child=n_parent+(Wchild-Wparent)*t+u,where(q-1)t=Bt,q⁴u=Xold',
  universal_center_cut='Zchild-qZparent=Hμ²[q⁴ΔW((q-1)t-Bt)+(q-1)(q⁴u-X)]',
  normalization='B=qBt,Mchild=qMparent,outputchild=q⁸outputparent whenlicensedcentercutvanishes',
  boundary='The qdivX conclusion isprovedonlyafterH|Kpos removesHdenominator. No positivepointwiseinverse isclaimed.'))
 files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,generator_sha256=digest(Path(__file__).read_bytes()),
  dependencies={n:dict(repository_path=str(p.relative_to(ROOT)),sha256=digest(files[n]))for n,p in deps.items()},
  coefficient_family='wholeoriginalcompact44; calibratedwholeBFSspecialization usesuniformsourceinterface',canonical_page_unchanged=True,
  boundary='Ordinaryunboundedproof only; no newLean/object-ZFC derivation. Separate107/340versus101/368costdegreetradeoff.'))
 files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=107,operation_breakdown=counts,exact_degree=340,syntactic_degree=degrees['N'],sha256={n:digest(v)for n,v in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
 for n,data in build().items():
  path=OUT/n
  if a.check:need(path.read_bytes()==data,'byte-identical '+n)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
 print(json.dumps(dict(status='PASS',check=a.check,positive_variables=10,operations=107,exact_degree=340),indent=2))
if __name__=='__main__':main()
