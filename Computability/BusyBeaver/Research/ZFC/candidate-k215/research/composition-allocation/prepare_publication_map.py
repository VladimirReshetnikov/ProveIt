#!/usr/bin/env python3
"""Own external static packet preparation only; no repository writes or proof runs."""
from pathlib import Path
import json,hashlib,shutil
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
OLD=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k216'
NEW=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21')
OUT=Path('/tmp/k215-publication-packet-pending');OUT.mkdir(exist_ok=False)
base=Path('Computability/BusyBeaver/Research/ZFC/candidate-k215');rows=[]
def add(src,rel):
 dst=OUT/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
 rows.append({'source':str(dst),'target':str(base/rel),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest(),'bytes':dst.stat().st_size,'original_source':str(src)})
for f in sorted((P/'held-publication').iterdir()):
 if f.is_file() and f.name!='freeze.json':add(f,Path(f.name))
for f in sorted((OLD/'licenses').iterdir()):
 if f.is_file():add(f,Path('licenses')/f.name)
for name in ['NOTICE.md','provenance/ATTRIBUTION.md','provenance/k217-NOTICE.md','provenance/parent-ATTRIBUTION.md']:
 f=OLD/name
 if f.exists():add(f,Path('provenance/partial-selector')/name)
for name in ['provenance/ATTRIBUTION.md','provenance/PREDECESSOR_ATTRIBUTION.md','provenance/K218_NOTICE.md','provenance/inputs.json','provenance/source_proof_review.md','provenance/source_proof_review.json','sections/source_calibration.tex']:
 add(NEW/name,Path('provenance/permuted-commands')/name)
for f in sorted(P.rglob('*')):
 if not f.is_file() or any(x in f.parts for x in ['solver-venv','__pycache__','held-publication']):continue
 if f.name=='prepare_publication_map.py':continue
 add(f,Path('research/composition-allocation')/f.relative_to(P))
for f in sorted(Path('/tmp/k215-fresh/run1/code').rglob('*')):
 if f.is_file() and '__pycache__'not in f.parts:add(f,Path('verification/code')/f.relative_to('/tmp/k215-fresh/run1/code'))
add(Path('/tmp/k215-fresh/run.py'),Path('verification/root-runner.py'))
add(Path(__file__),Path('research/composition-allocation/prepare_publication_map.py'))
assert len({r['target']for r in rows})==len(rows)
result={'status':'STATIC_PACKET_READY_FRESH_RESULT_PENDING','files':rows,'pending_fresh_records':{'root':'/tmp/k215-fresh/run1','files':['actual.json','before.json','runtime.log','preflight.json','runtime/startup.json','runtime/runtime.json','runtime/runtime_cases.json'],'note':'Do not install or pin mutable records until actualterminal. Full startup/cases may be deterministicgzip copies retaining raw hash.'},'remaining':'Root owns terminal evidence review, independent blank audit, final accepted-status prose and repository installation.'}
(OUT/'map.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'files':len(rows),'bytes':sum(r['bytes']for r in rows),'map_sha256':hashlib.sha256((OUT/'map.json').read_bytes()).hexdigest()},indent=2))
