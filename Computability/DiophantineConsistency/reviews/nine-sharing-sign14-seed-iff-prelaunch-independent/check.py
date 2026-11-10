#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-seed-iff-check';draft=root/'research/nine-sharing-sign14-seed-iff-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();r=p/'run.py';m=p/'source-manifest.json'
assert sha(r)=='6df2d882009491af649726ba1bc7d4751c38f8735149622b15e052f2967b2832' and sha(m)=='8687807b00709e3882492bbf7ee48de741aa79ce6bb5ef35b629e7e4768ba8c0'
row,=json.loads(m.read_text())['rows'];name='Sign14SeedExistential';src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and row['module']=='DiophantineConsistency.'+name and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign14ReverseBridge','DiophantineConsistency.Sign14TauLift'];assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem exists_same_input','(hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)','v 0 = x ∧ InternalZero (SharingSeed14Degree124.seed p) v','v 0 = x ∧ InternalZero (SharingSeed15Degree124.seed p) v','Sign14TauLift.exists_tau_of_seed','Sign14ZeroBridge.forward','Sign14ZeroBridge.backward'):assert t in s
assert all('(hp'+i+' : ((p '+i+' : ℤ) : DiffRing V) = ι ' in s for i in ('0','1','2','3'))
survey=p/'provider-survey.py';assert sha(survey)=='3b7036812923f7f4af9b11e90c99162140d4a0bd591f0c0087d5db92447ca593';runner=r.read_text();assert "'-M2800'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner and "survey['object_realpath']" in runner and "for rel,rec in survey['extra'].items():" in runner
for label,pin in [('zero-assembly-retry03','570c1f96d98e8c699dbc83d3f2440fa5a6b71de6b2e475d92e5e7935c2a9b35d'),('tau-lift','883ee1868879c0c42ff8b4828080e1fc67da3075c38d1d461845cacb21e779a8')]:
 c=root/('reviews/nine-sharing-sign14-'+label+'-terminal-independent/check.py');assert sha(c)==pin;subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
z=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,check=True,timeout=180);data=json.loads(z.stdout);assert data['status']=='PASS' and len(data['extra'])==6 and data['object_realpath'].endswith('/Sign14TauLift.olean')
x=subprocess.run([sys.executable,'-I','-S','-B',str(r),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','extra_overlays':6,'scope':'same-input existential iff under represented ports and bounds; no endpoint/file binding'},indent=2))
