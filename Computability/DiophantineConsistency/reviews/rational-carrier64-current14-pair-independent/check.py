#!/usr/bin/env python3
"""Read-only recheck of narrow conjunction, captured providers and resource receipt."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-current14-pair';a=p/'observations/attempt02';o=Path('/tmp/rational-carrier64-current14-pair-priority-check02')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
external=r/'research/rational-carrier64-current14-actual-external/observations/attempt01/result.json';state=Path('/tmp/current14-standard-fresh-build-20261104/state.json');manifest=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json')
pins={p/'RationalCarrier64CurrentPair.lean':'92cde64344af599049f535a6237dfeeb134e44bdc3c6506bc2c07ae1759ba35e',p/'check02.py':'b43bf7a70fd8d40219718cb241f84404f1ca389f70e5d7e879895190992b91af',a/'result.json':'0e3cccd62ef35352f9ccbe00639947f580ec5b1a2adeb05561a58a263a945593',a/'compile.log':'f37e120a0a57ab4ddbd4a1299dbb2d1137fafcba6b594e551771692bb34fdda0',o/'RationalCarrier64CurrentPair.olean':'da0337c6058b21c5ae5b31eed1fa4e3d69cfe3c02eb2fce469b5bae384fd4dc3',external:'b876bd365509fe34f4234b0f23d62eb0ba63acc7124a7b4c38b389717c7d63f7',state:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',manifest:'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',Path('/tmp/rational-carrier64-current14-actual-external-priority-check01/RationalCarrier64ActualExternal.olean'):'1486ef0d67c262527bd3cab26f6d0bfe4749fcfd8b9d068e3018c61dec1fa93c',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRAStandardCurrentEndpoint.olean'):'3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
outer=a/'outer-terminal.json'
if sha(outer)!='eb8c6ff96a7c66a5f74ae079c59e0d77960a804fc36540cf673a3894a3aa3e2f':raise ValueError('outer observation pin')
t=json.loads(outer.read_bytes())
if t['session_id']!=52835 or t['terminal_exit_code']!=0 or t['returned_session_id'] is not None:raise ValueError('outer terminal observation')
x=json.loads((a/'result.json').read_bytes()); e=json.loads(external.read_bytes()); b=json.loads(state.read_bytes()); m=json.loads(manifest.read_bytes()); mod='DiophantineConsistency.IPRAStandardCurrentEndpoint'; row=next(t for t in b['records'] if t['module']==mod)
if e['status']!='PASS' or e['exit']!=0 or e['object_sha256']!=pins[Path('/tmp/rational-carrier64-current14-actual-external-priority-check01/RationalCarrier64ActualExternal.olean')]:raise ValueError('external predecessor')
if b['status']!='PASS' or b['source_status']!='CURRENT_AT_FINAL_CHECK' or b['manifest_sha256']!=sha(manifest) or row['exit']!=0 or row['object_sha256']!=pins[Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRAStandardCurrentEndpoint.olean')]:raise ValueError('base endpoint')
src=Path('/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean'); work=r/'Lean/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean'
if sha(src)!=row['source_sha256'] or sha(work)!=row['source_sha256'] or m['sources'][mod]['sha256']!=row['source_sha256'] or sha(Path(row['log']))!=row['log_sha256']:raise ValueError('endpoint producer source/log')
if set(row['direct_inputs'])-{'Init'}!=set(m['sources'][mod]['imports']):raise ValueError('endpoint imports')
for v in row['direct_inputs'].values():
 if sha(Path(v['path']))!=v['sha256']:raise ValueError('endpoint input drift')
if x['status']!='PASS' or x['exit']!=0 or x['stop_reason'] is not None or not x['guards_stable'] or x['guards_before']!=x['guards_after'] or x['group_rss_samples']<1:raise ValueError('terminal')
if x['lean_memory_mib']!=2800 or '-M2800' not in x['command'] or x['sampled_group_rss_limit_bytes']!=7*1024**3//2 or x['sampled_peak_group_rss_bytes']>=x['sampled_group_rss_limit_bytes'] or x['minimum_memavailable_bytes']<10*1024**3:raise ValueError('resource receipt')
if (a/'result.json').read_bytes()!=(o/'result.json').read_bytes() or (a/'compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained copies')
for f,v in x['guards_after'].items():
 f=Path(f)
 if v is None:
  if os.path.lexists(f):raise ValueError(('shadow',str(f)))
 elif not f.is_file() or str(f.resolve())!=v['realpath'] or sha(f)!=v['sha256']:raise ValueError(('guard',str(f)))
log=(a/'compile.log').read_text().strip();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
if len(reports)!=1 or reports[0][0]!='DiophantineConsistency.RationalCarrier64CurrentPair.external_and_ipra' or ' '.join(reports[0][1].split())!='propext, Classical.choice, Quot.sound':raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(x['guards_after']),'recorded_lean_exit':x['exit'],'peak_sampled_rss':x['sampled_peak_group_rss_bytes'],'min_available':x['minimum_memavailable_bytes'],'object_sha256':x['object_sha256'],'scope':'Direct captured guards, endpoint producer and external receipt; no Lean replay or transitive audit.'},sort_keys=True,indent=2))
