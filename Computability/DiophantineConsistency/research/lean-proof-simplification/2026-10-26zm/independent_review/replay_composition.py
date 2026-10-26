#!/usr/bin/env python3
"""Self-contained zero-fuzz patch composition check; never invokes Lean or Lake."""
from pathlib import Path
import hashlib,json,subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent
FIX=HERE/'fixtures'
REL=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/SidonPositions.lean')
base=(FIX/'SidonPositions.original.lean').read_bytes()
expected='e3f637d5eaffc23facb5b0b4f901cee030bb6ee046dc544b9d34ed9b04f95c9f'
if hashlib.sha256(base).hexdigest() != expected:
 raise RuntimeError('Original Sidon source does not match frozen source SHA-256')
if shutil.which('patch') is None:
 raise RuntimeError('The source-only replay requires the standard patch executable')
receipts=[]; finals=[]
for sequence,patches in [('prior_then_round5',['sidon_assumed_prior.patch','sidon_round5.patch']),('round5_then_prior',['sidon_round5.patch','sidon_assumed_prior.patch'])]:
 with tempfile.TemporaryDirectory(prefix='sidon_composition_') as temporary:
  work=Path(temporary);dest=work/REL;dest.parent.mkdir(parents=True);dest.write_bytes(base)
  steps=[]
  for name in patches:
   p=FIX/name
   done=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(p)],cwd=work,text=True,capture_output=True)
   steps.append({'patch':'fixtures/'+name,'patch_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exit_code':done.returncode,'stdout':done.stdout,'stderr':done.stderr,'result_lines':len(dest.read_bytes().splitlines())})
   if done.returncode != 0:
    raise RuntimeError(f'Patch failed ({sequence}, {name}): {done.stdout} {done.stderr}')
  final=dest.read_bytes();finals.append(final)
  receipts.append({'sequence':sequence,'steps':steps,'final_sha256':hashlib.sha256(final).hexdigest()})
if finals[0] != finals[1]:
 raise RuntimeError('Patch composition orders are not byte-identical')
if len(finals[0].splitlines()) != 157:
 raise RuntimeError('Unexpected composed full-file line count')
if receipts[0]['steps'][0]['result_lines'] != 161:
 raise RuntimeError('Unexpected assumed-applied baseline line count')
result={'patches_commute_exact_bytes':True,'fuzz':0,'source_sha256':expected,'assumed_applied_baseline_lines':161,'round5_composed_lines':157,'new_lines_saved':4,'prior_lines_saved_not_reclaimed':7,'validation':'patch application and byte identity only; no Lean invocation','receipts':receipts}
(HERE/'composition_check.json').write_text(json.dumps(result,indent=2)+'\n')
(HERE/'SidonPositions.assumed_applied_plus_round5.lean').write_bytes(finals[0])
print(json.dumps({k:result[k] for k in ['patches_commute_exact_bytes','assumed_applied_baseline_lines','round5_composed_lines','new_lines_saved']},indent=2))
