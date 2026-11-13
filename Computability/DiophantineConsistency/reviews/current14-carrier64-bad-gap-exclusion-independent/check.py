#!/usr/bin/env python3
import hashlib,gzip,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-bad-gap-exclusion';gp=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={'Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3','Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462'}
assert sha(gp)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'check.py')=='d18476cec72a14d332f8d953e96f8d0e1e38655f2cccc00ff07b1feb712f99cc'
base=Path('/tmp/p72-current-base-extension-attempt02-20261105');survey=json.loads((root/'research/p72-current-base-source-survey/result.json').read_text());snapshot=json.loads((root/'research/p72-current-base-extension-build-attempt02/terminal/source-snapshot.json').read_text());progress=json.loads((root/'research/p72-current-base-extension-build-attempt02/terminal/progress.json').read_text());assert progress['status']=='PASS' and progress['completed']==progress['total']==681
for fn,ph in pins.items():
 source=root/'Lean/DiophantineConsistency'/fn;assert sha(source)==ph;mod='DiophantineConsistency.'+fn.removesuffix('.lean').replace('/','.');i=survey['extension_order'].index(mod);row=json.loads((base/'rows'/f'{i:04d}.json').read_text());assert row['module']==mod and row['status']=='PASS' and row['source_sha256']==snapshot[mod]==ph and sha(base/'src'/Path(*mod.split('.')).with_suffix('.lean'))==ph
 obj=base/'lib'/Path(*mod.split('.')).with_suffix('.olean');assert sha(obj)==row['object_sha256']
 for run in row['runs']:assert run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'] and sha(run['log'])==run['log_sha256']
 for path,v in row['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 log=(base/'logs'/f'{i:04d}-compile.txt').read_text();target='P72Exact.indices_ordinary' if 'Exact' in mod else 'P72Power.power_of_mod';assert target in log and 'sorryAx' not in log and 'error:' not in log
# Reread exact theorem binders, including all premises used in the review.
t=(root/'Lean/DiophantineConsistency/Compact44/P72Exact.lean').read_text().split('theorem indices_ordinary',1)[1].split(':= by',1)[0]
for h in ('hq3','hX','hy0','hYq','hη','hc','hi\'','hf','ha','hR26','hny','hks','hRμ','hnmod','hmy','hg','hs\'','haux'):assert '('+h in t
u=(root/'Lean/DiophantineConsistency/Compact44/P72Power.lean').read_text().split('theorem power_of_mod',1)[1].split(':= by',1)[0]
for h in ('hX16','hY0','hζ','hk','hc','hH','ha','hny','hn13','hnR','hmR','hmx','hmy','hgmod'):assert '('+h in u
assert 'Exp.exp R' in u and 'theorem cast_exp' in (root/'Lean/DiophantineConsistency/ArithmeticStandardCasts.lean').read_text()
# Authenticate current binary port payloads, reproduce fixed arithmetic independently.
g=json.loads(gp.read_text());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 packed=(gp.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==meta['gzip_sha256'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
beta,K,mc,mf=(ports[n] for n in ('beta','K0','MC','MF'));q=beta+1;F=1;C=2*q-1;w=1+(q-2)*K;z=3+K*(2*q-1);b=q-1;G=q*(q-F)-C;R=G*(q*q-1)+mc+q*mf;X=w*q;Y=q**3;E=X*Y
assert beta==(1<<94517)-1 and q>=32 and w>1 and w%2==1 and R%2==1 and R>=26 and R+1<E and (K+w)*C+q-F-z*b==1 and X.bit_length()==283975 and R.bit_length()==378068 and R>=X.bit_length()
# Independently check signed-absolute-difference encoding on all small valid positive inputs.
for f in range(1,6):
 for c in range(2,8):
  for T in range(1,7):
   for R0 in range(1,7):
    V=f*f*(c*T-R0)-c;A=f*f*T*c;B=f*f*R0+c
    for y in range(abs(V)+1,abs(V)+5):
     u0=y-V;assert u0>0 and abs(A-B)==abs(V) and abs(A+u0-B)==y
# Run independently audited graph rewrite packet, which binds the whole 64-gate graph and its conditional nature.
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier64-transport-proposal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=json.loads((pkg/'result.json').read_text());out=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not out.stderr and json.loads(out.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'fixed family exclusion and general rank-window necessity conditional on source theorem application; no new Lean theorem or global reverse equivalence'},indent=2))
