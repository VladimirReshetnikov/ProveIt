#!/usr/bin/env python3
"""Own one-time exact-copy publication of completed evidence; no supplied invocation."""
from pathlib import Path
import hashlib,json,shutil
SRC=Path('/tmp/zfc-intake190-opening')
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
HOST=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
CODE=HOST/'code/intake190-fresh-k218';DATA=HOST/'data/intake190-fresh-k218'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def main():
 assert json.loads((SRC/'execution/result.json').read_text())['status']=='FRESH_DIRECT_LEAVES_PASS'
 assert not CODE.exists() and not DATA.exists();CODE.mkdir();DATA.mkdir();records=[]
 def copy(a,b):
  assert a.is_file() and not b.exists();b.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(a,b);assert a.read_bytes()==b.read_bytes()
  records.append({'original':str(a),'target':str(b.relative_to(ROOT)),'sha256':sha(b),'size':b.stat().st_size})
 for p in sorted((SRC/'code').iterdir()):copy(p,CODE/p.name)
 for p in sorted((SRC/'review').iterdir()):copy(p,(CODE if p.suffix=='.py' else DATA/'review')/p.name)
 for name in ('plan.json','result.json'):copy(SRC/'execution'/name,DATA/'execution'/name)
 for folder in ('logs','output'):
  for p in sorted((SRC/'execution'/folder).rglob('*')):
   if p.is_file():copy(p,DATA/'execution'/p.relative_to(SRC/'execution'))
 for p in sorted((SRC/'history/prepare-attempt1').iterdir()):
  if p.is_file():copy(p,DATA/'history/prepare-attempt1'/p.name)
 plan=json.loads((SRC/'execution/plan.json').read_text())
 for x in plan['inputs']:
  p=Path(x['path']);assert sha(p)==x['sha256']
  copy(p,DATA/'input-snapshots'/p.relative_to(SRC/'execution'))
 report={'status':'EXACT_FRESH_SOURCE147_EVIDENCE_PUBLICATION_PASS','reviewer':'opening_encoder','source':147,'batch':190,
 'actual_result_sha256':sha(SRC/'execution/result.json'),'review_sha256':sha(SRC/'review/review.json'),
 'files':records,'count':len(records),'bytes':sum(x['size'] for x in records),
 'scope':'Exact selected fresh leaf evidence and portable preparation/runner. Raw scratch paths retained verbatim as execution history. No supplied wrapper, manifests, ancestor suites or proof-assistant runs.',
 'history':'Own initial path-only preparation failure retained with original helper and narrow diffs; incomplete packet copy omitted as duplicated delivered bytes, and no supplied job started in that attempt.'}
 dump(DATA/'publication.json',report)
 print(DATA/'publication.json',sha(DATA/'publication.json'),len(records))
if __name__=='__main__':main()
