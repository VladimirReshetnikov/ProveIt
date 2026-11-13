#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-other-weights-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8207b4358988e28462f5fb69642ea2002ab18ce2cdda4f264d22f9f87ae40ffe' and sha(p/'source-manifest.json')=='45d9330fac9562f690764da38cd16936d3936b3336f06e7b3e4f7b0b59681572'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65OtherWeights';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65QInputs'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Expr.constant (p 0) * .var 0','q p - .var 1 - .var 2','a p ^ 2 + H p','E p * k * Y p','(b p * (q p - .var 1) + .var 2) * (q p ^ 2 - 1)','(Expr.constant (p 2) + q p * Expr.constant (p 3)) * .var 0','E p * .var 9 + k - rank p','.var 4 ^ 2 * (c p * .var 6 - rank p) - c p','.var 5 * delta p * c p ^ 2','tau p ^ 2 - ell p * (ell p + k)','S p ^ 2 * (V p ^ 2 - .var 12 ^ 2) + .var 12 ^ 2','(Expr.constant (p 1) + .var 8) * C p + (q p - .var 1) - .var 3 * b p','delta p * .var 4 ^ 2 - S p ^ 2'):assert z in s
w={'delta':12,'rank':4,'tau':7,'V':8,'S':23,'P':22,'U':62,'W':2,'Z':46};assert (2*6,max(max(1+1,1)+2,max(0,1+0)+1),max(6+1,1,4),max(2+max(5+1,4),5),1+12+2*5,max(2*7,(6+1+4)*2),2*23+max(2*8,2),2,max(12+2,2*23))==tuple(w.values())
for n0,val in w.items():assert re.search(r'theorem '+n0+r'_weight .*weightedDegree weight = '+str(val),s)
for f in ('current14-carrier65-q-inputs-retry-terminal-independent','current14-carrier65-q-fields-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','weights':w,'scope':'standalone non-Q syntax weights only; Carrier65 evaluator/degree binding separate'},indent=2))
