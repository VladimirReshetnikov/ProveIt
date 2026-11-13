#!/usr/bin/env python3
"""Offline artifact/header reachability audit; never invokes Lean."""
import collections,hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; p=r/'research/nine-variable-external-matrix-preflight'
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
pins={'direct-result.json':'8fc9a8a1978eecd0ddfb58928a5f2aa113a0a757dd4e7b63d1aeb120df76f787','header-result.json':'7c5751dfd7002b3425e71f462f8058078ee0911e5f4ecbcd1e66871a4832b9fe','header-observation.json':'b9608a987e17b93f18e226c15457449a7a031eb71dfcbab2189cda109b06054e','header.log':'c14a9ae93ea9a4fda45389c867f5a14029246ed4c6c7aa38332eda54ee82393d','analysis-result.json':'2f03aa6bd00a0a6b661b533e7a18f6a4ea112e9430f884e8f76dec22f8219a2c'}
for f,h in pins.items():
 if sha(p/f)!=h:raise ValueError(('pin',f))
d=json.loads((p/'direct-result.json').read_bytes()); h=json.loads((p/'header-result.json').read_bytes()); a=json.loads((p/'analysis-result.json').read_bytes());o=json.loads((p/'header-observation.json').read_bytes());term=json.loads((p/'terminal-observation.json').read_bytes())
if d['status']!='PASS_DIRECT_DEPS_NOT_IMPORT_CHECK' or d['exit']!=0 or d['guards_before']!=d['guards_after'] or len(d['guards_after'])!=750:raise ValueError('direct status/guards')
if o['exit']!=0 or o['stop_reason'] is not None or not o['inputs_stable'] or o['input_hashes_before']!=o['input_hashes_after'] or o['result_sha256']!=pins['header-result.json'] or o['log_sha256']!=pins['header.log']:raise ValueError('header terminal observation')
for path,expected in o['input_hashes_before'].items():
 if sha(Path(path))!=expected:raise ValueError(('header source drift',path))
for name,path in {'lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),'probe':p/'DirectExternalProbe.lean','runner':p/'deps.py','survey':r/'research/nine-variable-current-base-source-survey/result-final.json'}.items():
 if sha(path)!=d['inputs'][name]:raise ValueError(('direct source drift',name))
if term['header_session_id']!=76951 or term['header_outer_exit']!=0 or term['direct_probe_exit']!=0 or term['analysis_exit']!=0:raise ValueError('outer observation')
if a['status']!='PASS_PARTIAL_ANALYSIS' or h['status']!='PARTIAL_COMPILED_HEADERS' or len(h['modules'])!=64 or len(h['frontier'])!=199 or len(set(h['frontier']))!=199:raise ValueError('partial scope')
if set(h['seeds'])!=set(d['selected'])-{'Init'} or len(h['seeds'])!=24:raise ValueError('seeds')
if set(h['frontier'])!=set(n for m in h['modules'].values() for n in m['imports'])-set(h['modules']):raise ValueError('frontier')
for name,rec in h['modules'].items():
 if sorted(set(n for x in rec['headers'].values() for n in x['imports']))!=rec['imports']:raise ValueError(('header union',name))
 if name in h['seeds'] and rec['path']!=d['selected'][name]['path']:raise ValueError(('selection',name))
for name,rec in d['selected'].items():
 count=d['counts'][name]
 if count!=(2 if name=='Init' else 1):raise ValueError(('multiplicity',name))
 x=Path(rec['path']); old=d['guards_after'][str(x)]
 if rec['realpath']!=old['realpath'] or rec['sha256']!=old['sha256']:raise ValueError(('direct guard',name))
 if name!='Init' and rec['root']!=1:raise ValueError(('seed root',name))
def check_guards(guards, kind):
 for raw,v in guards.items():
  x=Path(raw)
  if v is None:
   if os.path.lexists(x):raise ValueError((kind,'unexpected',raw))
   continue
  if not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError((kind,'identity',raw))
  if 'size' in v and (x.stat().st_size!=v['size'] or x.stat().st_mtime_ns!=v['mtime_ns']):raise ValueError((kind,'metadata',raw))
check_guards(d['guards_after'],'direct');
oldpath=r/'reviews/current14-matrix-import-order-probe/result.json'
if sha(oldpath)!='914339a67b5a866cb577de5e12b79a0212cb725c4307ae87c699e539efefe20d':raise ValueError('historic matrix evidence pin')
old=json.loads(oldpath.read_bytes())
if len(old['provider_guards'])!=20:raise ValueError('historic guard count')
for path,previous in old['provider_guards'].items():
 current=d['guards_after'].get(path,'MISSING')
 if previous is None:
  if current is not None:raise ValueError(('historic absent',path))
 elif current=='MISSING' or current is None or previous['sha256']!=current['sha256'] or previous['realpath']!=current['realpath']:raise ValueError(('historic identity',path))
if a['provider_guards_before']!=a['provider_guards_after'] or len(a['provider_guards_after'])!=1920:raise ValueError('analysis guards')
check_guards(a['provider_guards_after'],'analysis')
for raw,rec in h['artifacts'].items():
 x=Path(raw)
 if rec is None:
  if os.path.lexists(x):raise ValueError(('artifact unexpectedly exists',raw))
 elif not x.is_file() or sha(x)!=rec['sha256'] or str(x.resolve())!=rec['metadata']['realpath']:raise ValueError(('header artifact',raw))
targets={'Foundation.Vorspiel.Matrix','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber'}
for seed in set(h['seeds'])-targets:
 seen=set();todo=[seed];found=set();unknown=set()
 while todo:
  x=todo.pop()
  if x in seen:continue
  seen.add(x)
  if x in targets:found.add(x);continue
  if x not in h['modules']:unknown.add(x);continue
  todo.extend(h['modules'][x]['imports'])
 if found or not unknown or a['reachability'][seed]['known_paths_to_matrix'] or set(a['reachability'][seed]['unexpanded_reachable'])!=unknown:raise ValueError(('reachability',seed))
if [c['module'] for c in a['visited_object_collisions']]!=['Init'] or a['visited_object_collisions'][0]['different_hashes']:raise ValueError('collision claim')
print(json.dumps({'status':'PASS_PARTIAL_PREFLIGHT_ARTIFACT_AUDIT','visited':64,'frontier':199,'direct_seeds':24,'direct_guards':750,'visited_candidate_guards':1920,'header_artifacts':len(h['artifacts']),'new_seed_reachability_unknown':22,'scope':'Rechecked retained files and partial graph; no Lean replay, transitive completeness, or Matrix compatibility conclusion.'},sort_keys=True,indent=2))
