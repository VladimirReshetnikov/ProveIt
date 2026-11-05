#!/usr/bin/env python3
"""Independently inspect ten-stage source and retained terminal artifacts; no Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-seed38-weighted-retry';T=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105');A=P/'attempt01';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,s):
 if not x:raise RuntimeError(s)
need(sha(A/'state.json')==sha(T/'state.json')=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534','state')
need(sha(P/'run.py')=='8e1b2963e8dc9f9a406f3bea29ba3cae24fab3cb06e7a16ca3e8e11fe0dbf999' and sha(P/'source-manifest.json')=='9c00d40c96d65f202b76e5fd378ebdf14a9345dd555949e1382395599183420c','runner and manifest')
outer=A/'outer-terminal-author-record.json';need(sha(outer)=='e8fc0ae5c39389a9a9a7027c449d4bf718e201813d92659cbea515928f5edcce','outer record');ob=json.loads(outer.read_text());need(ob['outer_session_id']==30685 and ob['outer_exit_code']==0 and ob['runner_status']=='PASS','author outer observation')
s=json.loads((A/'state.json').read_text());es=json.loads((P/'source-manifest.json').read_text())['rows'];need(s['status']=='PASS' and len(s['rows'])==len(es)==10 and s['runner_sha256']==sha(P/'run.py'),'terminal result')
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
seen={};warn=0;guard_count=0
for e,r in zip(es,s['rows']):
 n=r['module'];f=T/'src/DiophantineConsistency'/(n+'.lean');workspace=P/'src/DiophantineConsistency'/(n+'.lean');need(e['module']=='DiophantineConsistency.'+n and sha(f)==sha(workspace)==e['source_sha256']==r['source_sha256'],'source '+n);imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',f.read_text(),re.M);need(imports==e['imports'],'imports '+n);need(set(r['dependencies'])-{'Init'}==set(imports)-{'Init'},'dependency set '+n)
 for typ in ('deps','compile'):
  v=r[typ];log=T/(n+'-'+typ+'.txt');need(v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'],'exit '+n+typ);need(sha(log)==sha(A/(n+'-'+typ+'.txt'))==v['log_sha256'],'log '+n+typ)
  if typ=='compile':
   text=log.read_text();need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",text),'errors '+n);warn+=len(re.findall(r'warning:',text))
 for mod,dep in r['dependencies'].items():
  f=Path(dep['path']);need(f.is_file() and str(f.resolve())==dep['realpath'] and sha(f)==dep['sha256'],'dependency '+mod)
  if mod in seen:need(dep['sha256']==seen[mod] and str(f)==str(T/'lib'/Path(*mod.split('.')).with_suffix('.olean')),'stage route '+mod)
 for path,v in r['direct_guard'].items():
  guard_count+=1;f=Path(path)
  if v is None:need(not os.path.lexists(f),'absence '+path)
  else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'guard '+path)
 out=T/'lib/DiophantineConsistency'/(n+'.olean');need(sha(out)==r['object_sha256'],'object '+n);seen[e['module']]=r['object_sha256']
need(warn==5,'warning count');need(not any('#print axioms' in (P/'src/DiophantineConsistency'/(r['module']+'.lean')).read_text() for r in s['rows']),'unexpected axiom report')
print(json.dumps({'status':'PASS_SCOPED_TERMINAL_REVIEW','stages':len(es),'log_count':20,'guard_slots':guard_count,'overlay_links':len(s['overlay_links']),'warnings':warn,'outer_session':'author-recorded 30685 exit 0','axiom_reports':'none','scope':'Retained stage observations and exact theorem source; no Lean replay or complete dynamic ancestry.'},sort_keys=True,indent=2))
