#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign15-signed-aux-ingredient-check';draft=root/'research/nine-sharing-sign15-signed-aux-ingredient-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();r=p/'run.py';m=p/'source-manifest.json';assert sha(r)=='49beaeefec7be3b6432d6b8974590a1aeab4e519f39cd46c68446fa9072c438b' and sha(m)=='f03d3f2dcf3294c0a92ac408ae6a1cf3e1446fa92b799e64aef13d1d0e7595f8';row,=json.loads(m.read_text())['rows'];name='Sign15SignedAux';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign33AbsDiffSquare']
assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
for x in ('theorem absdiff_signed_square (f c T r : V)','theorem auxiliary_norm_of_signed (f c T r S y : V)','(hNa : ι y*ι y','Sign33AbsDiffSquare.absdiff_sq','set_option maxHeartbeats 4000000'):assert x in s
assert 'inner :' not in s and 'nonneg_iff' not in s
runner=r.read_text();assert "'-M2800'" in runner and "'-j1'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner and 'free>=5_000_000_000' in runner
check=root/'reviews/nine-sharing-sign33-absdiff-square-terminal-frontier-independent/check.py';assert sha(check)=='e8c61292b389d2233fd8ce05c868be35128b0c020e958ea7578325ae675deb87';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(r),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic signed Na auxiliary norm ingredient only; no seed extraction, natural lift, bridge or iPRA'},indent=2))
