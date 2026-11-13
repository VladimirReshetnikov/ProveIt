#!/usr/bin/env python3
"""Read-only assembly retry and 12 successful producer audit; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-gates-assembly-retry';B=D/'research/nine-sharing-norm38-gates-batched-draft';T=Path('/tmp/nine-sharing-norm38-gates-batched-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','f2786d839a3e78a69036fb654cbb5296b7057457330699b5221193ecac3c7dfc'),(P/'source-manifest.json','84f0fc45d645c7adf54b5bf5bfa52ad61d966e120207de3e54f40cea85e041ad'),(P/'src/DiophantineConsistency/Norm38GatesAssembly.lean','c5dec04f7956dac3572fdcf45ef1c763c2c76c41e7e6705c9e2a56e3a948b639'),(B/'attempt01/state.json','fc4e64a0bb36abdff0d51a21e29bebd4d8771f688f9a0a8fc56d700731317e65'),(B/'attempt01/Norm38GatesAssembly-compile.txt','f3d63406f34662ff384ecab409d95a6252353db1676ffe7f5ee478951e6a1293'),(B/'attempt01/outer-terminal-author-record.json','bc7c2460940f8b86a3f86e6f2c0f61506ecf020b06b6f02e65862dd752e811b0')]:need(sha(p)==h,'pin '+str(p))
f='src/DiophantineConsistency/Norm38GatesAssembly.lean';old=(B/f).read_text();new=(P/f).read_text();a='gate80 p ports w hp hz⟩';b='gate80 p ports w hp hz, by simp⟩';need(old.count(a)==1 and new==old.replace(a,b),'source delta');need([int(i) for i in re.findall(r'gate(\d+) p ports w hp hz',new)]==list(range(21,81)),'60 ordered gates');m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==1 and m[0]['module']=='DiophantineConsistency.Norm38GatesAssembly' and m[0]['source_sha256']==sha(root/m[0]['source']) and m[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',new,re.M) and len(m[0]['imports'])==12,'manifest')
s=json.loads((B/'attempt01/state.json').read_text());o=json.loads((B/'attempt01/outer-terminal-author-record.json').read_text());need(sha(T/'state.json')==sha(B/'attempt01/state.json') and s['status']=='FAILED' and len(s['rows'])==13 and o['outer_session_id']==42976 and o['outer_exit_code']==1,'failed state');last=s['rows'][-1];log=(B/'attempt01/Norm38GatesAssembly-compile.txt').read_text();need(last['module']=='Norm38GatesAssembly' and last['deps']['exit']==0 and last['compile']['exit']==1 and last['compile']['stop_reason'] is None and not last.get('object_sha256') and '∀ (a : Gate (Fin 81)), True' in log,'failed assembly')
guards=0
for i,row in enumerate(s['rows'][:12]):
 n=row['module'];need(n==f'Norm38Gates{i:02}' and sha(T/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(T/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'source/object '+n)
 for typ in ('deps','compile'):
  v=row[typ];need(v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'],'outcome '+n+typ);need(sha(T/(n+'-'+typ+'.txt'))==sha(B/'attempt01'/(n+'-'+typ+'.txt'))==v['log_sha256'],'log '+n+typ)
 for path,v in row['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'guard absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
r=(P/'run.py').read_text();need("base['rows']=base['rows'][:12]" in r and "base['rows'][-1]['compile']['exit']==1" in r and "guard(deps)==row['direct_guard']" in r,'runner selection');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','successful_producers':12,'gate_facts':60,'guard_slots':guards,'overlay_links':len(s['overlay_links']),'scope':'Source and retained producer point checks; no Lean or model bridge.'},indent=2,sort_keys=True))
