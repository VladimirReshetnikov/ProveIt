#!/usr/bin/env python3
"""Pin the six surveyed additions for a provisional single-author extension."""
from pathlib import Path
import hashlib
import json
import subprocess

D=Path(__file__).resolve().parent
ROOT=D.parents[3]
SURVEY=D/'survey-receipt.json'
POLICY=D/'extension/task-policy.json'
OUTPUT=D/'author-additions.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
survey=json.loads(SURVEY.read_text())
policy=json.loads(POLICY.read_text())
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
order=survey['additional_project_modules']
assert len(order)==6 and order[-1]==policy['target'] and not survey['direct_external_not_in_parent']
sources={}
for name in order:
    row=survey['sources'][name]; rel=row['workspace_path']; path=ROOT/rel
    blob=subprocess.check_output(['git','show',commit+':'+rel],cwd=ROOT)
    sha=hashlib.sha256(blob).hexdigest()
    assert path.is_file() and H(path)==sha==row['source_sha256'],name
    sources[name]={'workspace_path':rel,'sha256':sha,'imports':row['imports']}
out={'status':'FROZEN_ADDITIONS','source_commit':commit,'order':order,'sources':sources,
     'axiom_reports':{policy['target']:policy['expected_axiom_names']},
     'scope':'Six tracked sources only; parent snapshot and proof are not audited by this planner.'}
assert not OUTPUT.exists()
OUTPUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('FROZEN_ADDITIONS',len(order),H(OUTPUT))
