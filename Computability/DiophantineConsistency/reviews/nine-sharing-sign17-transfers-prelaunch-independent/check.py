#!/usr/bin/env python3
"""Review nine staged row aliases and transfers without author parser or Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-transfers-check';draft=research/'nine-sharing-sign17-transfers-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();old=research/'nine-sharing-sign18-degree94-root-candidate/seed.json';new=research/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(old)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb' and sha(new)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';a=json.loads(old.read_text())['residuals'];b=json.loads(new.read_text())['residuals'];indices=[i for i in range(len(a)) if i!=6];assert a[6]['gate']=='V2minusY2' and len(a)==9 and len(b)==8 and [a[i]['gate'] for i in indices]==[x['gate'] for x in b]
m=p/'source-manifest.json';assert sha(m)=='b9ae6883deb67ca636738835de6d3f07d3ba95717a6c7bf3a0444cc21f0b270f';rows=json.loads(m.read_text())['rows'];assert len(rows)==8
for i,(entry,row) in enumerate(zip(rows,b)):
 name=f'Sign17Transfer{i:02}';g=row['gate'];j=indices[i];src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert entry['module']=='DiophantineConsistency.'+name and sha(src)==sha(draft/(name+'.lean'))==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign17Coordinate']
 assert f'def old{g} (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row{j:02} p' in s and f'def new{g} (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row{i:02} p' in s
 oldclaim=f'SharingSeed18Degree94.firstResidual p = old{g} p' if j==0 else f'((SharingSeed18Degree94.remainingResiduals p).drop {j-1}).head? = some (old{g} p)';assert oldclaim in s
 newclaim=f'SharingSeed17Degree96.firstResidual p = new{g} p' if i==0 else f'((SharingSeed17Degree96.remainingResiduals p).drop {i-1}).head? = some (new{g} p)';assert newclaim in s
 assert f'theorem {g}_eval ' in s and '(hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17))' in s and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
runner=p/'run.py';assert sha(runner)=='049d9bb5fe47c2dfe956beb599ac48ac67c4e4712ce857a74a0b1a0e08d62da2';r=runner.read_text();assert "if local=='Sign17Coordinate':" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-coordinate-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':8,'runner_sha256':sha(runner),'scope':'eight conditional source row transfers, coordinate provider and guards; no Lean transfer/endpoint'},indent=2,sort_keys=True))
