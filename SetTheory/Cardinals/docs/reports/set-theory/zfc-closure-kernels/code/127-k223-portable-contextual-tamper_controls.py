#!/usr/bin/env python3
from pathlib import Path
import json,shutil,subprocess,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'fold_binding';D=H/'tamper_controls';D.mkdir(exist_ok=True)
results=[]
for kind in ('control','new_write_flip','old_write_flip','missing_row','uncovered_guard','wrong_trace','noninductive_fact','constrained_start'):
 C=D/kind;F=C/'fold_0';F.mkdir(parents=True,exist_ok=True)
 for name in('candidate.tm','sites.json'):shutil.copyfile(B/name,C/name)
 for name in('candidate.tm','sites.json','local_proof.json','recipe.json'):shutil.copyfile(B/'fold_0'/name,F/name)
 p=F/'local_proof.json';x=json.loads(p.read_text())
 if kind in('new_write_flip','old_write_flip'):
  t=(F if kind=='new_write_flip'else C)/'candidate.tm';lines=t.read_text().splitlines();fields=lines[1].split();fields[2]=str(1-int(fields[2]));lines[1]=' '.join(fields);t.write_text('\n'.join(lines)+'\n')
 elif kind=='missing_row':x['row_proofs'].pop()
 elif kind=='uncovered_guard':x['row_proofs'][0]['branches'][0]['guard']['99']=0
 elif kind=='wrong_trace':x['row_proofs'][0]['branches'][0]['trace'][0][3]^=1
 elif kind=='noninductive_fact':x['invariant']['1']['99']=0
 elif kind=='constrained_start':x['invariant']['0']['0']=0
 if kind!='control':p.write_text(json.dumps(x,indent=2)+'\n')
 run=subprocess.run(['python3','-B',str(H/'replay_local_certificate.py'),str(C),str(C/'replay.json')],capture_output=True,text=True)
 (C/'stdout.log').write_text(run.stdout);(C/'stderr.log').write_text(run.stderr)
 expected=0 if kind=='control' else 1
 if (run.returncode==0)!=(expected==0):raise RuntimeError((kind,run.returncode,run.stdout,run.stderr))
 results.append(dict(case=kind,exit_code=run.returncode,accepted=run.returncode==0,last_error=run.stderr.splitlines()[-1]if run.stderr else None))
r=dict(status='PASS_POSITIVE_AND_SEVEN_TAMPER_CONTROLS',results=results,checker_sha256=hashlib.sha256((H/'replay_local_certificate.py').read_bytes()).hexdigest(),scope='Seven deliberate corruption classes are rejected; an untouched independent copy passes. These tests exercise proof validation, not TM execution sampling.')
(H/'tamper_controls.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
