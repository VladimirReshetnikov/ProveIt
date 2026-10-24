#!/usr/bin/env python3
"""Remove the redundant v-square argument from the signed14 guard, only in a new sibling."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/constructive-integer14-quadratic-shared'
OUT=ROOT/'candidates/constructive-integer14-guard-reduced'
PARENT_SHA='307015e68eb300713d06076b0c3c78f1017fe74dbe79f6b89385292637d1ec41'
OPS={'add','sub','mul'}
def need(p,s):
 if not p:raise ValueError(s)
def sha(b):return sha256(b).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(sha(raw)==PARENT_SHA,'immutable119parent')
 parent=json.loads(raw);old=parent['nodes'];nm=parent['named_registers'];G,Gv=nm['G'],nm['Gv']
 v=next(i for i,r in enumerate(old)if r==['variable','v'])
 v2=next(i for i,r in enumerate(old)if r==['mul',v,v]);need(old[Gv]==['mul',G,v2],'actualguardargument')
 need([i for i,r in enumerate(old)if r[0]in OPS and v2 in r[1:]]==[Gv],'v²singleuse')
 nodes=[];mapping={};records=[]
 for i,row in enumerate(old):
  if i==v2:records.append(dict(parent=i,status='removed_private',old_row=row));continue
  if i==Gv:
   mapping[i]=mapping[G];records.append(dict(parent=i,status='guard_alias',child=mapping[G],replacement_parent=G,old_row=row));continue
  newrow=[row[0],mapping[row[1]],mapping[row[2]]]if row[0]in OPS else deepcopy(row)
  mapping[i]=len(nodes);nodes.append(newrow);records.append(dict(parent=i,status='retained',child=mapping[i]))
 child=deepcopy(parent);counts=dict(Counter(r[0]for r in nodes if r[0]in OPS))
 child.update(name='signed14_guard_without_v_square_degree312',nodes=nodes,output=mapping[parent['output']],
              named_registers={k:mapping[i]for k,i in nm.items()if k!='Gv'},operations=sum(counts.values()),operation_counts=counts,
              parent_sha256=PARENT_SHA,proof='PROOF.md',
              proof_status='New ordinary integer-existence equivalence: norm/core unchanged; guard argument v²G replaced by G; four private guard witnesses regenerated. No new Lean/native/internal-ZFC proof.')
 need(len(nodes)==144 and child['operations']==117,'actual117operations')
 files={'equation.json':encoded(child),'source/parent-equation.json':raw}
 copies={'source/parent-README.md':'README.md','source/ordinary-proof.md':'source/ordinary-proof.md',
         'source/ancestor-proof.md':'source/parent/PROOF.md','source/parent-CHECK.json':'CHECK.json',
         'source/parent-CHECK_OPTIMIZED.json':'CHECK_OPTIMIZED.json','source/parent-MANIFEST.json':'MANIFEST.json',
         'source/independent_norm_oracle.py':'source/independent_norm_oracle.py','source/LICENSE.UPSTREAM':'source/parent/LICENSE',
         'coefficients/BINDING.json':'coefficients/BINDING.json'}
 for target,source in copies.items():files[target]=(PARENT/source).read_bytes()
 for pin in json.loads(files['coefficients/BINDING.json'])['payloads'].values():
  rel='coefficients/'+pin['file'];files[rel]=(PARENT/rel).read_bytes()
 files['NODE_REMAP.json']=encoded(dict(schema='signed_guard_argument_substitution_v1',parent_sha256=PARENT_SHA,
     all_parent_nodes=records,deleted_v_square_parent=v2,aliased_guard_argument_parent=Gv,
     replacement_parent=G,retired_named_register='Gv',
     relation='Every core/norm node is identical; only guard descendants change under the explicit substitution Gv:=G. No pointwise equality of the complete old/new polynomial is asserted.'))
 files['SOURCE_PINS.json']=encoded(dict(parent='candidates/constructive-integer14-quadratic-shared',parent_equation_sha256=PARENT_SHA,
     parent_manifest_sha256=sha((PARENT/'MANIFEST.json').read_bytes()),
     original_ordinary_proof_sha256=sha(files['source/ordinary-proof.md']),
     complete_six_port_binding_sha256=sha(files['coefficients/BINDING.json'])))
 files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=sha(Path(__file__).read_bytes()),
     integer_variables=14,operations=117,exact_degree=312,norm_degree=256,
     sha256={name:sha(raw)for name,raw in sorted(files.items())}))
 return files

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 for name,raw in build().items():
  p=OUT/name
  if args.check:need(p.read_bytes()==raw,'deterministicallyrebuild '+name)
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 print(json.dumps(dict(status='PASS',check=args.check,integer_variables=14,operations=117,exact_degree=312)))
if __name__=='__main__':main()
