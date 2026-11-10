#!/usr/bin/env python3
"""Review nine staged row aliases and transfers without author parser or Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign18-transfers-check';draft=research/'nine-sharing-sign18-transfers-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();old=research/'nine-sharing-sign19-degree44-y-candidate/seed.json';new=research/'nine-sharing-sign18-degree94-root-candidate/seed.json';assert sha(old)=='01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1' and sha(new)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb';a=json.loads(old.read_text())['residuals'];b=json.loads(new.read_text())['residuals'];assert a[0]['gate']=='main_root' and len(a)==10 and len(b)==9 and [x['gate'] for x in a[1:]]==[x['gate'] for x in b]
m=p/'source-manifest.json';assert sha(m)=='b77f58da2ab3c36e302fab8ba31d671ee2e7b64048a4c1b0f910265720c3a9a3';rows=json.loads(m.read_text())['rows'];assert len(rows)==9
for i,(entry,row) in enumerate(zip(rows,b)):
 name=f'Sign18Transfer{i:02}';g=row['gate'];src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert entry['module']=='DiophantineConsistency.'+name and sha(src)==sha(draft/(name+'.lean'))==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign18Coordinate']
 assert f'def old{g} (p : Fin 4 → ℤ) : Expr (Fin 20) := SharingSeed19Degree44.row{i+1:02} p' in s and f'def new{g} (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row{i:02} p' in s
 assert f'((SharingSeed19Degree44.remainingResiduals p).drop {i}).head? = some (old{g} p)' in s
 expected=f'SharingSeed18Degree94.firstResidual p = new{g} p' if i==0 else f'((SharingSeed18Degree94.remainingResiduals p).drop {i-1}).head? = some (new{g} p)';assert expected in s
 assert f'theorem {g}_eval ' in s and '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
runner=p/'run.py';assert sha(runner)=='58982e993503acee7f8a516c0f5a9cd6cdb551dd28f7f0aeb01e6c9ff7dfee15';r=runner.read_text();assert "if local=='Sign18Coordinate':" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign18-coordinate-retry03-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':9,'runner_sha256':sha(runner),'scope':'nine source row transfers, coordinate provider and guards; no Lean transfer/endpoint'},indent=2,sort_keys=True))
