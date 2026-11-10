#!/usr/bin/env python3
"""Review sign17 generic axis-degree ingredient guard without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-degree-core-check';draft=root/'research/nine-sharing-sign17-axis-degree-core-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='bc24cab9163cc63004cc3b464e6ee57d2e67156dca7cd4f2cc3fa27285005451' and sha(m)=='ca01016a325fd28612ae8b8480efdea481860deaf7667eb524eb8b5ac08a8e22';row,=json.loads(m.read_text())['rows'];name='Sign17AxisDegreeCore';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']=='fb6070c652b4e5d551ad7307e5baecd085e23064c730951feeb150b7b9aa565f' and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign17DegreeCompose'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
for t in ('theorem product_degree (p q : P) (hp : 0 < p.totalDegree) (hq : 0 < q.totalDegree)','theorem dominant_add (p q : P) (h : q.totalDegree < p.totalDegree)','theorem shift_degree : shift.totalDegree = 1','theorem base_degree (z : ℤ) (hz : z ≠ 0) : (base z).totalDegree = 1'):assert t in s
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and r.count('check_external_syntax()')>=3
# Stale sign20 local routing is unreachable from the one manifest import.
assert "elif local in ('Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard')" in r and row['imports']==['DiophantineConsistency.Sign17DegreeCompose']
check=root/'reviews/nine-sharing-sign17-degree-staged-retry-terminal-independent/check.py';assert sha(check)=='0510b85b20108976a1cdf627bb9f0cf97f044c033eec83997f541eda46d4399a';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(run),'scope':'generic degree core, base requires z nonzero; no concrete lower bound or binding'},indent=2,sort_keys=True))
