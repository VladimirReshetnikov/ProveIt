#!/usr/bin/env python3
"""Recheck cleared-pair output and direct provenance without Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-cleared-pair';a=p/'observations/attempt01';o=Path('/tmp/rational-carrier64-cleared-pair-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
prior=r/'research/rational-carrier64-cleared-ipra/observations/attempt01/result.json';priorouter=prior.parent/'outer-terminal.json';pair=r/'research/rational-carrier64-current14-pair/observations/attempt02/result.json';state=Path('/tmp/current14-standard-fresh-build-20261104/state.json');outer=a/'outer-terminal.json'
pins={p/'ClearedCurrentPair.lean':'fb35fe4a8c8bfa1995265109485853a7b906728a9e1e87140d096b415be2f079',p/'check01.py':'2a2c83e7c504cc47fb2c73ce11f92a28772dba946a1d2f0f4b42f87991ab428f',a/'result.json':'de1c08b733e08df60462a56f1a3640187106f3400c00654f9b5d198a4ed5e602',a/'compile.log':'9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087',outer:'86b0b1817754f554c1818a5a15e21ae9722238f7c8f7e81f56c0b57d606a5807',o/'ClearedCurrentPair.olean':'6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb',prior:'57e8509112bf368c21425ab22c4611a269f506a92da7ec9c3e656b3f4e630d8b',priorouter:'fbaa7de6b563da8cca95bc219d69e3cf41a6fbb7e1fb0ad5b78a0cb24f6c1126',pair:'0e3cccd62ef35352f9ccbe00639947f580ec5b1a2adeb05561a58a263a945593',state:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',Path('/tmp/rational-carrier64-cleared-ipra-priority-check01/ClearedCurrentIPRA.olean'):'d895d103bb0a8b888c205c4c7c33bbcdf8a9bbcd735c687475dc6fd96175b1f5',Path('/tmp/rational-carrier64-current14-pair-priority-check02/RationalCarrier64CurrentPair.olean'):'da0337c6058b21c5ae5b31eed1fa4e3d69cfe3c02eb2fce469b5bae384fd4dc3',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentEquationSyntax2011.olean'):'28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentKernelData2011.olean'):'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
for f in (prior,pair):
 v=json.loads(f.read_bytes())
 if v['status']!='PASS' or v['exit']!=0 or v['stop_reason'] is not None or not v['guards_stable']:raise ValueError(('prior receipt',str(f)))
for f,session in ((outer,53951),(priorouter,52395)):
 v=json.loads(f.read_bytes())
 if v['session_id']!=session or v['terminal_exit_code']!=0 or v['returned_session_id'] is not None:raise ValueError(('outer',str(f)))
b=json.loads(state.read_bytes())
if b['status']!='PASS' or b['source_status']!='CURRENT_AT_FINAL_CHECK':raise ValueError('base state')
x=json.loads((a/'result.json').read_bytes())
if x['status']!='PASS' or x['exit']!=0 or x['stop_reason'] is not None or not x['guards_stable'] or x['guards_before']!=x['guards_after'] or x['group_rss_samples']<1:raise ValueError('terminal')
if x['lean_memory_mib']!=2800 or '-M2800' not in x['command'] or x['sampled_peak_group_rss_bytes']>=x['sampled_group_rss_limit_bytes'] or x['minimum_memavailable_bytes']<10*1024**3:raise ValueError('resource guard')
if (a/'result.json').read_bytes()!=(o/'result.json').read_bytes() or (a/'compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained copies')
for f,v in x['guards_after'].items():
 f=Path(f)
 if v is None:
  if os.path.lexists(f):raise ValueError(('shadow',str(f)))
 elif not f.is_file() or str(f.resolve())!=v['realpath'] or sha(f)!=v['sha256']:raise ValueError(('guard',str(f)))
log=(a/'compile.log').read_text().strip();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
if len(reports)!=1 or reports[0][0]!='DiophantineConsistency.ClearedCurrentPair.external_and_cleared_ipra' or ' '.join(reports[0][1].split())!='propext, Classical.choice, Quot.sound':raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(x['guards_after']),'recorded_lean_exit':x['exit'],'outer_session':53951,'outer_exit':0,'object_sha256':x['object_sha256'],'scope':'Direct guards and predecessor observations; no Lean replay or full transitive audit.'},sort_keys=True,indent=2))
