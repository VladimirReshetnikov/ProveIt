#!/usr/bin/env python3
"""Review generic sign16 absdiff transport candidate without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign16-absdiff-ingredient-retry01-check';draft=root/'research/nine-sharing-sign16-absdiff-ingredient-retry01-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='7806fc94dff36cf85efdddf690f92e1cc252ce4535578cde82b592571d6168cb' and sha(m)=='0cf3e5b59731679ef051ce7b3cf673e6b8e77d64fa01c563dfea083c00cdc015';row,=json.loads(m.read_text())['rows'];name='Sign16AbsDiffIngredient';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign33AbsDiffSquare'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
assert 'theorem absdiff_V_square (f c T r inner : V)' in s and 'theorem auxiliary_norm_of_signed (f c T r inner S y : V)' in s and s.count('(hinner : ι inner = ι c * ι T - ι r)')==2 and '(hNa : ι y*ι y' in s and 'Sign33AbsDiffSquare.absdiff_sq' in s
r=run.read_text();assert "'-M2800'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'free>=5_000_000_000' in r and 'matches=[x for x in base[\'rows\'] if x[\'module\']==local]' in r and "sha(P/'source-manifest.json')" in r
prior=(root/'research/nine-sharing-sign16-absdiff-ingredient-draft/Sign16AbsDiffIngredient.lean').read_text()
assert prior.split('  linear_combination hNa + (ι S)*(ι S)*hs')[0]==s.split('  have hdiff :')[0]
assert prior.split('end DiophantineConsistency.Sign16AbsDiffIngredient')[1]==s.split('end DiophantineConsistency.Sign16AbsDiffIngredient')[1]
failure=root/'reviews/nine-sharing-sign16-absdiff-ingredient-failure-independent/check.py'
assert sha(failure)=='dfc6c0bcc0b016f33e511c85b9dc325e43adad50c77c39ab407b3a44ff28f2de'
subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
check=root/'reviews/nine-sharing-sign33-absdiff-square-terminal-frontier-independent/check.py';assert sha(check)=='e8c61292b389d2233fd8ce05c868be35128b0c020e958ea7578325ae675deb87';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(run),'scope':'generic absdiff square and signed auxiliary norm under explicit inner and norm hypotheses; no candidate AST extraction, bridge or iPRA result'},indent=2,sort_keys=True))
