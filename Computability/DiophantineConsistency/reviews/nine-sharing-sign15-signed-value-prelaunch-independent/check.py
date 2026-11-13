#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign15-signed-value-check';draft=root/'research/nine-sharing-sign15-signed-value-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();r=p/'run.py';m=p/'source-manifest.json';assert sha(r)=='089a4a7e90bb2b08b0dac632c65bf76a05c9b5f67c23415e632fc0e2c104d0b3' and sha(m)=='df901d1eb3317c37708ff60270e6f91a1bc3dfec7bd6bcbdd14377e77bcfaa42';row,=json.loads(m.read_text())['rows'];name='Sign15SignedValue';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']=='a2ae0bfa5a335d0c0bef6dd438d855405ce0e2642495c17ac6828ecfc76c4676' and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign15RankValue'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
for t in ('theorem inner_eval','theorem signed_eval','(shared31 p).evalRing','(shared33 p).evalRing','ι (C beta v) * ι (v 7 + 1) - ι (Sign15RankValue.Rank beta MC MF v)','(hq : v 2 + 1 ≤ A beta v)'):assert t in s
assert all(s.count('(hp'+i+' : ((p '+i+' : ℤ) : DiffRing V) = ι ')==2 for i in ('0','2','3')) and 'inner :' not in s
runner=r.read_text();assert "'-M2800'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner and 'free>=5_000_000_000' in runner
check=root/'reviews/nine-sharing-sign15-rank-value-terminal-independent/check.py';assert sha(check)=='c3c29de0db4e64e14b10715b4fed210c68f7307119e6bff116b0d997309ada17';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(r),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'difference-ring signed inner/V evaluations under represented ports and q≥F; no natural witness or lift'},indent=2))
