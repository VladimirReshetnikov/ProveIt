#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-tau-value-check';draft=root/'research/nine-sharing-sign14-tau-value-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();r=p/'run.py';m=p/'source-manifest.json';assert sha(r)=='e44b22271b92018079aea3307796333a2f78a9245b3f44d105d670576509ed1b' and sha(m)=='25b51c78b67ead9993b3d7fd253f7a587968bb53a2b17a05c510499623675054';row,=json.loads(m.read_text())['rows'];name='Sign14TauValue';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']=='12af3642a50bd16acaa0347ee1d2750b8d257f381189364ab52cae2f95afc86d' and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign14RankValue'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
for t in ('theorem e_eval','theorem tau_eval','(shared18 p).evalRing','(shared36 p).evalRing','(hq : v 2 + 1 ≤ A beta v)','Sign14RankValue.rank_eval'):assert t in s
assert all('(hp'+i+' : ((p '+i+' : ℤ) : DiffRing V) = ι ' in s for i in ('0','2','3')) and 'gap :' not in s
runner=r.read_text();assert "'-M2800'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner
c=root/'reviews/nine-sharing-sign14-rank-value-terminal-independent/check.py';assert sha(c)=='5874d46d00bf3d46e3242e4cd49abec9e0e2942c4070c60a89fbb095deec18e3';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(r),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'signed tau value under represented ports and q≥F; no natural witness or lift'},indent=2))
