#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-w-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='888eb4d686dd50060fa0ba7cbb0cf505c0bd10c18a1db619773a2b4a36185ae3' and sha(p/'source-manifest.json')=='99757d043a41da5e3bff7f40c2e40bacc56b74323e20d671b26c241259989bbe'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalW';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalBinding'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(Polynomial.C K + Polynomial.X) *','Polynomial.C beta * Polynomial.X + 1 - Polynomial.X - Polynomial.X','Polynomial.X * (Polynomial.C beta * Polynomial.X)','Polynomial.C (-2) * Polynomial.X ^ 2','K * (beta - 2) + beta','Polynomial.C (K + 1)','(w beta K).coeff 2 = -2','(w beta K).natDegree = 2','(axisCore p).W = w (p 0) (p 1)','(axisCore p).W.natDegree = 2'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-diagonal-binding-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual W diagonal coefficient -2 and degree 2 at arbitrary ports'},indent=2))
