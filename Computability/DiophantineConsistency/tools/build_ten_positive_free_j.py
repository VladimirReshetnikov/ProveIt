#!/usr/bin/env python3
"""Build the positive free-J sibling by deleting two pinned affine gates."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-quadratic-projection-shared'
OUT=ROOT/'candidates/ten-positive-free-j'
PAGE=ROOT/'candidates/one-page-scaled10'
PARENT_SHA='507cb56d69f0af5f678bc2984f1b5061d21751581543679ee99c8d9111fe0045'

def need(ok,message):
 if not ok:raise ValueError(message)
def digest(x):return sha256(x).hexdigest()
def encoded(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 raw=(PARENT/'equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'entire frozen105 parent')
 old=json.loads(raw);need(old['source'][:2]==[['2j','*',2,'j'],['J','+','2j',1]],'exact affine J prefix')
 need(all('j'not in row[2:]and'2j'not in row[2:]for row in old['source'][2:]),'no other use of deleted private/input names')
 child=deepcopy(old);child.update(name='ten_positive_free_J_degree408',
  witnesses=['J']+old['witnesses'][1:],source=old['source'][2:],operations=103,
  operation_breakdown=dict(Counter(row[1]for row in old['source'][2:])),parent_sha256=PARENT_SHA,
  proof_status='Ordinary positive-zero/refutation equivalence via deferred coprimality and recovered odd main index; exactP_old(j)=P_free(2j+1). No new Lean/internal-ZFC proof.',
  proof='PROOF.md')
 need(child['operation_breakdown']=={'*':60,'+':25,'-':18},'actual103 operation census')
 files={'equation.json':encoded(child),'source/parent-equation.json':raw}
 deps={
 'source/QUADRATIC_PROOF.md':PARENT/'source/ordinary-proof.md',
 'source/ORIGINAL_PROOF.md':PARENT/'source/original-proof.md',
 'source/SOURCE61.tex':ROOT/'con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex',
 'source/SOURCE61_MANIFEST.json':ROOT/'con-zfc-diophantine-forms/61-congruence-carriers/MANIFEST.json',
 'source/LICENSE_SOURCE61':ROOT/'con-zfc-diophantine-forms/61-congruence-carriers/LICENSE',
 'source/NOTICE_SOURCE61.md':ROOT/'con-zfc-diophantine-forms/61-congruence-carriers/NOTICE.md',
 'source/parent-check.json':PARENT/'CHECK.json',
 'source/parent-check-optimized.json':PARENT/'CHECK_OPTIMIZED.json',
 'source/independent_norm_oracle.py':PARENT/'source/independent_norm_oracle.py',
 'source/BFS_SOURCE_TRANSFER.md':PAGE/'README.md',
 'source/BFS_SOURCE_PINS.json':PAGE/'SOURCE_PINS.json',
 'source/BFS_TUPLE_VERIFY.json':PAGE/'TUPLE_VERIFY.json',
 'source/ORDINARY_PEER.md':ROOT/'reviews/ten-positive-free-j-ordinary-peer.md',
 'source/ORDINARY_PEER.json':ROOT/'reviews/ten-positive-free-j-ordinary-peer.json',
 }
 for name,path in deps.items():files[name]=path.read_bytes()
 files['coefficients/BINDING.json']=(PARENT/'coefficients/BINDING.json').read_bytes()
 for pin in old['coefficient_binding']['ports'].values():
  name='coefficients/'+pin['file'];files[name]=(PARENT/name).read_bytes()
 files['PREFIX_REMAP.json']=encoded(dict(parent_sha256=PARENT_SHA,
  parent_input='j',child_input='J',affine_relation='J=2*j+1',
  parent_polynomial_identity='P_parent(j,rest)=P_child(2*j+1,rest)',
  deleted_rows=[dict(parent_index=i,row=old['source'][i])for i in range(2)],
  computed_parent_J_becomes_child_input_J=True,
  retained_rows=[dict(parent_index=i,child_index=i-2,register=r[0])for i,r in enumerate(old['source'])if i>=2],
  child_norm_tail_start=90,parent_norm_tail_start=92,
  semantics='Complete polynomial affine identity over every commutative ring. The enlarged positive J-domain is justified separately by PROOF.md, includingJ1.'))
 files['PROVENANCE.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
  generator_sha256=digest(Path(__file__).read_bytes()),
  dependencies={name:dict(repository_path=str(path.relative_to(ROOT)),sha256=digest(files[name]))for name,path in deps.items()},
  original_compact44=True,canonical_page_unchanged=True,
  bfs_scope='Same arithmetic proof applies to the wholeBFS tuple satisfyingbeta>=31 and its separately checked uniformsource61theorem. The actualpolynomialhereusesoriginalcompact44; noKvalueidentityasserted.',
  source_theorem_scope='SOURCE61 thm:source accepts every strictly positiveJ;N>1/oddrepunit promises occur only in canonicalcompleteness.',
  boundary='No new Lean or encoded object-ZFC derivation. Ordinary inherited native/refutation calibration remains explicit.'))
 files['BUILD.json']=encoded(dict(status='PASS',positive_variables=10,operations=103,
  operation_breakdown=child['operation_breakdown'],exact_degree=408,
  sha256={name:digest(data)for name,data in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
 for name,data in build().items():
  path=OUT/name
  if args.check:need(path.read_bytes()==data,'byte-identical '+name)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
 print(json.dumps(dict(status='PASS',check=args.check,positive_variables=10,operations=103,exact_degree=408),indent=2))

if __name__=='__main__':main()
