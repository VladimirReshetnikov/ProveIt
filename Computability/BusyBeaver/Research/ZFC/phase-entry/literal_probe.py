#!/usr/bin/env python3
"""Prepared literal mutant prefixes, not reached-from-blank or runtime proof."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json,hashlib
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if not __debug__:parser.error('Keep assertions enabled')
ROOT=args.repo.resolve();OUT=args.output.resolve()
if OUT==ROOT or ROOT in OUT.parents:parser.error('External scratch output required')
OUT.mkdir(parents=True,exist_ok=True)
BASE=ROOT/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as A
import permutation252_continuations as P
raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()==A.EXPECTED_SHA
original=A.read_table(raw);nodes=P.read_nodes(ROOT/P.PROGRAM)
phase_path=BASE/'results/permutation252-phase-analysis.json'
phase=json.loads(phase_path.read_text())
masks=phase['mask_classes'][phase['site_mask_class_ids'][-1]]
assert masks==[7,7,7,1,6,1,7,1,7]
records=[]
for action in [(1,'L',229),(1,'R',77),(1,'R',252)]:
 for n,k in [(1,0),(1,1),(2,0),(2,1)]:
  table=dict(original);table[172,1]=action
  recipe=(204,action[2],8390,'1111111111',(0,0,0,0,n,0,k,0,0))
  assert all(mask & (1 if value==0 else 2 if value==1 else 4) for mask,value in zip(masks,recipe[-1],strict=True))
  got=P.literal_probe(table,nodes,recipe,20000)
  got['source_masks_satisfied']=True
  got['incoming_action']=list(action)
  records.append(got)
r={'scope':'Twelve20k-bounded literal changed-table prefixes from preparedframes. Registers satisfy unary phase masks but are not proved reachablefromblank. Firstcleanframe mismatch only excludes exactone-instructionboundary; it is not global nonequivalence.','table_sha256':A.EXPECTED_SHA,'fuel':20000,'case8390_unary_masks':masks,'phase_evidence_sha256':hashlib.sha256(phase_path.read_bytes()).hexdigest(),'records':records}
(OUT/'literal-results.json').write_text(json.dumps(r,indent=2)+'\n')
for q in records:
 print(q['incoming_action'],q['logical_values'][4],q['logical_values'][6],json.dumps(q['outcome']))
