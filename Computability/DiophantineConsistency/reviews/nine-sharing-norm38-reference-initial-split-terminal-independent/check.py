#!/usr/bin/env python3
"""Read-only eight-stage initial-agreement artifact audit; no Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-reference-initial-split-check';A=P/'attempt01';T=Path('/tmp/nine-sharing-norm38-reference-initial-split-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','d7aa2fce5da1f35a97431a40116de9a9e6a7c307ff4522755a375e61503691f8'),(P/'source-manifest.json','34e2044c2fae104edb929f97944eff1fcf3794a46eacdf408880b6067a4aee99'),(A/'state.json','ca49ec6fa785a5ad3eff917d313e83db38464cff16209a646115a8e19cc89d55'),(A/'outer-terminal-author-record.json','1ff76f3b9a40a374b204bc2513af312f0b0cb3f729554ea37135e403a4aff1c3')]:need(sha(p)==h,'pin '+str(p))
need(sha(T/'state.json')==sha(A/'state.json'),'temporary state');s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal-author-record.json').read_text());need(s['status']=='PASS' and len(s['rows'])==8 and o['outer_session_id']==3891 and o['outer_exit_code'] is None and o['runner_stdout']=='PASS norm38 split reference-initial diagnostic','terminal state/author observation')
m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==8,'manifest');prior={};guards=warnings=0
for i,(e,r) in enumerate(zip(m,s['rows'])):
 n=r['module'];need(n==(f'Norm38ReferenceInitialGroup{i:02}' if i<7 else 'Norm38ReferenceInitialAll') and e['module']=='DiophantineConsistency.'+n,'order');src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==sha(root/e['source'])==sha(T/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'],'source '+n);need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'],'imports '+n)
 for typ in ('deps','compile'):
  v=r[typ];log=A/(n+'-'+typ+'.txt');need(v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'],'exit '+n+typ);need(sha(log)==sha(T/(n+'-'+typ+'.txt'))==v['log_sha256'],'log '+n+typ)
  if typ=='compile':warnings+=log.read_text().count('warning:');need(not re.search(r'(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$',log.read_text()),'compile error '+n)
 for mod,dep in r['dependencies'].items():
  q=Path(dep['path']);need(q.is_file() and str(q.resolve())==dep['realpath'] and sha(q)==dep['sha256'],'dep '+mod)
  short=mod.split('.')[-1]
  if short in prior:need(dep['sha256']==prior[short] and q==T/'lib/DiophantineConsistency'/(short+'.olean'),'fresh stage route '+mod)
 for path,v in r['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 obj=T/'lib/DiophantineConsistency'/(n+'.olean');need(sha(obj)==r['object_sha256'],'object '+n);prior[n]=r['object_sha256']
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
need(warnings==19,'warning count');final=(P/'src/DiophantineConsistency/Norm38ReferenceInitialAll.lean').read_text();orig=(D/'research/nine-sharing-norm38-reference-initial-check/src/DiophantineConsistency/Norm38ReferenceInitial.lean').read_text();pat=r'theorem initial_agreement .*? := by';a=re.search(pat,final,re.S);b=re.search(pat,orig,re.S);need(a and b and a.group()==b.group(),'exact final theorem');need([int(x) for x in re.findall(r'exact initial_node(\d\d) ports w',final)]==list(range(21)),'21 node coverage');need(prior['Norm38ReferenceInitialAll']=='be80de6feaa282e9b1fa15a265474cecd4f1b20e50d846d78faa049fcbd0a100','final object');log=(A/'Norm38ReferenceInitialAll-compile.txt').read_text();need(log=="'DiophantineConsistency.Norm38Reference.initial_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axiom report')
active=[]
for proc in Path('/proc').iterdir():
 if proc.name.isdecimal():
  try:
   parts=(proc/'cmdline').read_bytes().split(b'\0')
   if any(x.endswith(b'/nine-sharing-norm38-reference-initial-split-check/run.py') for x in parts):active.append(proc.name)
  except (FileNotFoundError,ProcessLookupError,PermissionError):pass
need(not active,'runner currently visible')
print(json.dumps({'status':'PASS_SCOPED_TERMINAL_ARTIFACT_REVIEW','stage_count':8,'node_claims':21,'direct_guard_slots':guards,'overlay_links':len(s['overlay_links']),'warnings':warnings,'outer_numeric_exit':None,'runner_process_at_audit':'not observed in /proc sample','scope':'Recorded stage exits and artifacts, author-recorded PASS stdout; outer numeric exit unavailable and no Lean replay.'},sort_keys=True,indent=2))
