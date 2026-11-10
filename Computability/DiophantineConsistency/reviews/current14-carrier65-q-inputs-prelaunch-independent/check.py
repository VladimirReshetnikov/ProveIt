#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-inputs-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='74b53bbb43982139f89533cd0214fc8bfc20a973dd2a732b53d41207e0907e5b' and sha(p/'source-manifest.json')=='56094b293e81bf8fe0e18bd231ce63221faa138f832c4e32dbb159d861c23dd4'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QInputs';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.WeightedExpressionDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Expr.constant (p 0) * .var 0 + 1','.var 8 * q p','.var 7 * q p ^ 3','X p * Y p','.var 10 + .var 11','k * Y p + .var 10','E p + Y p','4 * a p + 3'):assert z in s
c=(root/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert all(z in c for z in ('let b := p 0 * J','let q := b + 1','let X := w * q','let Y := s * q ^ 3','let E := X * Y','let k := eta + zeta','let c := k * Y + eta','let a := E + Y','let H := 4 * a + 3'))
weights={'q':1,'X':2,'Y':4,'E':6,'c':5,'a':6,'H':6};assert (max(0+1,0),1+1,1+3*1,2+4,max(1+4,1),max(6,4),max(0+6,0))==tuple(weights.values())
for n0,val in weights.items():assert re.search(r'theorem '+n0+r'_weight .*weightedDegree weight = '+str(val),s)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '948b4e01db000ecf59395fc5555f51bf4b249f8922c40f40bbd6585b190b5772' in r
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not z.stderr and json.loads(z.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','weights':weights,'scope':'standalone syntax weights only; evaluator/actual polynomial degree binding separate'},indent=2))
