#!/usr/bin/env python3
"""Recheck frozen cleared-syntax client, predecessor receipts and captured guards."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-cleared-ipra';a=p/'observations/attempt01';o=Path('/tmp/rational-carrier64-cleared-ipra-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pair=r/'research/rational-carrier64-current14-pair/observations/attempt02/result.json';pairouter=pair.parent/'outer-terminal.json';bind=r/'research/rational-carrier64-current14-base-draft/observations/attempt04/result.json';base=Path('/tmp/current14-standard-fresh-build-20261104/state.json');outer=a/'outer-terminal.json'
pins={p/'ClearedCurrentIPRA.lean':'1f8e69d01966a3d933ac7d6c12f010b0374831502c1f96f8da5f8afb15fb70d7',p/'check01.py':'f9adc7f18ca8fee344c438e7abb75d9729d8bbf495a1e8035c74d3a25efb972a',a/'result.json':'57e8509112bf368c21425ab22c4611a269f506a92da7ec9c3e656b3f4e630d8b',a/'compile.log':'cda4a16e1ed9579a3c8bc6380d9f5821f33f29e84b4b46579a427e22713e60d3',outer:'fbaa7de6b563da8cca95bc219d69e3cf41a6fbb7e1fb0ad5b78a0cb24f6c1126',o/'ClearedCurrentIPRA.olean':'d895d103bb0a8b888c205c4c7c33bbcdf8a9bbcd735c687475dc6fd96175b1f5',pair:'0e3cccd62ef35352f9ccbe00639947f580ec5b1a2adeb05561a58a263a945593',pairouter:'eb8c6ff96a7c66a5f74ae079c59e0d77960a804fc36540cf673a3894a3aa3e2f',bind:'1aa7f92b832669e21aebae740f5df7ffad372d0ccd76ca7a196d2f58ae0d1ca0',base:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',Path('/tmp/rational-carrier64-current14-pair-priority-check02/RationalCarrier64CurrentPair.olean'):'da0337c6058b21c5ae5b31eed1fa4e3d69cfe3c02eb2fce469b5bae384fd4dc3',Path('/tmp/rational-carrier64-current14-base-priority-check04/RationalCarrier64Current.olean'):'ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRAStandardCurrentEndpoint.olean'):'3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentEquationSyntax2011.olean'):'28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
for f in (pair,bind):
 a0=json.loads(f.read_bytes())
 if a0['status']!='PASS' or a0['exit']!=0 or a0['stop_reason'] is not None or not a0['guards_stable']:raise ValueError(('prior receipt',str(f)))
for f,session in ((outer,52395),(pairouter,52835)):
 t=json.loads(f.read_bytes())
 if t['session_id']!=session or t['terminal_exit_code']!=0 or t['returned_session_id'] is not None:raise ValueError(('outer',str(f)))
b=json.loads(base.read_bytes())
if b['status']!='PASS' or b['source_status']!='CURRENT_AT_FINAL_CHECK':raise ValueError('base state')
x=json.loads((a/'result.json').read_bytes())
if x['status']!='PASS' or x['exit']!=0 or x['stop_reason'] is not None or not x['guards_stable'] or x['guards_before']!=x['guards_after'] or x['group_rss_samples']<1:raise ValueError('terminal')
if x['lean_memory_mib']!=2800 or '-M2800' not in x['command'] or x['sampled_peak_group_rss_bytes']>=x['sampled_group_rss_limit_bytes'] or x['minimum_memavailable_bytes']<10*1024**3:raise ValueError('resources')
if (a/'result.json').read_bytes()!=(o/'result.json').read_bytes() or (a/'compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained copies')
for f,v in x['guards_after'].items():
 f=Path(f)
 if v is None:
  if os.path.lexists(f):raise ValueError(('shadow',str(f)))
 elif not f.is_file() or str(f.resolve())!=v['realpath'] or sha(f)!=v['sha256']:raise ValueError(('guard',str(f)))
log=(a/'compile.log').read_text().strip();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
expected=['DiophantineConsistency.ClearedCurrentIPRA.'+n for n in ('cleared_eval','clearedNoZero_eq_noZero14','cleared_ipra')]
if [n for n,_ in reports]!=expected or any(' '.join(v.split())!='propext, Classical.choice, Quot.sound' for _,v in reports):raise ValueError('axiom reports')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(x['guards_after']),'recorded_lean_exit':x['exit'],'outer_session':52395,'outer_exit':0,'object_sha256':x['object_sha256'],'scope':'Captured direct guards, prior receipts and outer observations; no Lean replay or full transitive audit.'},sort_keys=True,indent=2))
