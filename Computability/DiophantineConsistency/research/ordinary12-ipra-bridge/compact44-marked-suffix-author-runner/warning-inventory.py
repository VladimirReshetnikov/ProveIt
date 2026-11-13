#!/usr/bin/env python3
"""Inventory all suffix source identities against one verified historical state and the stopped attempt; no Lean."""
import hashlib,importlib.util,json,re,sys
from pathlib import Path
if not __debug__ or sys.flags.optimize:raise ValueError('optimized Python rejected')
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('suffix_runner',HERE/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
scan=m.PLAN/'source-scan.json';state=m.HIST/'state.json';attempt=HERE/'evidence-attempt02'
if H(scan)!=m.PINS['plan_scan'] or H(state)!=m.PINS['history_state'] or H(attempt/'build-progress.json')!='8b88fe5c896137fc509b79ed095ed3283045ce6601101ee476ce916241229029' or H(attempt/'terminal-observation.json')!='16156864ef377150e565f3d600e6ca5680b21d73cd920a3c634e3a95c525a3a6':raise ValueError('inventory input drift')
bases=m.warning_baseline();manifest=json.loads(scan.read_text());records=json.loads(state.read_text())['records'];steps=json.loads((attempt/'build-progress.json').read_text())['steps'];rows=[]
if len(manifest['sources'])!=22 or len(steps)!=16:raise ValueError('inventory source or attempt count')
for i,r in enumerate(manifest['sources'],1):
 name=r['module'];sha=r['sha256'];source=Path(r['source'])
 if H(source)!=sha:raise ValueError(('source drift',name))
 candidates=[x for x in records if x.get('module')==name and x.get('source_sha256')==sha and x.get('exit')==0 and x.get('verified') is True]
 historic=[]
 for x in candidates:
  log=m.HIST/'logs'/x['log_file']
  if not log.is_file() or H(log)!=x['log_sha256']:raise ValueError(('historical log drift',name))
  lines=log.read_text();paths=[v for v in x['command'] if v.endswith('/'+name.split('.')[-1]+'.lean')]
  if len(paths)!=1:raise ValueError(('historical source path',name))
  normal=lines.replace(paths[0],'<SOURCE>');historic.append({'state_record_exit':0,'verified':True,'log':str(log.relative_to(m.REPO)),'log_sha256':H(log),'warning_count':lines.count('warning:'),'normalized_output_sha256':hashlib.sha256(normal.encode()).hexdigest()})
 current=None
 if i<=len(steps):
  x=steps[i-1];log=attempt/Path(x['log']).name
  if x['module']!=name or H(log)!=x['log_sha256']:raise ValueError(('attempt mismatch',name))
  text=log.read_text();current={'compiler_exit':x['compiler_exit'],'warning_count':text.count('warning:'),'wrapper_accepted':'output_slots' in x,'log':str(log.relative_to(m.REPO)),'log_sha256':H(log)}
  if name in bases and text.count('warning:'):
   old=str(Path(x['compiler_command'][-3]));normalized=text.replace(old,'<SOURCE>');current['matches_pinned_full_output']=normalized==bases[name]
 rows.append({'position':i,'module':name,'source_sha256':sha,'historical_verified_exact_source_records':historic,'second_attempt':current,'warning_policy':'exact full historical output only' if name in bases else 'reject any warning'})
print(json.dumps({'status':'PASS_NO_LEAN_22_SOURCE_WARNING_INVENTORY','source_scan_sha256':H(scan),'historical_state_sha256':H(state),'historical_scope':'Only ha87-isolated-full-author-pass verified exit-zero records were systematically searched; no match means no record in that state, not no historical build anywhere. Current attempt is author-only, not independent.','source_count':len(rows),'history_matched_count':sum(bool(x['historical_verified_exact_source_records']) for x in rows),'policy_modules':sorted(bases),'rows':rows,'lean_launched':False},indent=2,sort_keys=True))
