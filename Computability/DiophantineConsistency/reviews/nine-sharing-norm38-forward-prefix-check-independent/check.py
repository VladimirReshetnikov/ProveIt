#!/usr/bin/env python3
"""Read-only prefix/source/provider checks; no Lean invocation."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-forward-prefix-check';src=q/'src/DiophantineConsistency/Norm38ForwardPrefix.lean';draft=D/'research/nine-sharing-norm38-forward-bridge-draft/Norm38Forward.lean';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in [(src,'9662cd703c6ba4b8e0a164ac57d05223871070bcf1667bfd246c01425c4f6266'),(q/'source-manifest.json','b208355ea7fff041c05d66644d2104e082682ff18f98f13e777ed5f84261e4c1'),(q/'run.py','633317d4b99130dd0a09422e73ddc4c268708f8cc094bf844eeee4af7397f7e6'),(draft,'70dad9e40dd83aaca364972a1b84ba62f40594aeb5ad3b62b992e66078821837')]:assert sha(p)==h
def theorem(t):return re.search(r'^theorem forward_prefix\b.*?(?=^/--|^end )',t,re.M|re.S).group().strip()
assert theorem(src.read_text())==theorem(draft.read_text())
state=D/'research/nine-sharing-norm38-forward-gates-draft/attempt01/state.json';assert sha(state)=='42bf82193bf5eef3af518b5a6cffb240ab531975e82fd42afb2e531f675cc07c';s=json.loads(state.read_text());assert s['status']=='PASS' and len(s['rows'])==13;base=Path('/tmp/nine-sharing-norm38-forward-gates-20261105')
for r in s['rows']:
 n=r['module'];assert r['deps']['exit']==r['compile']['exit']==0;assert sha(base/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(base/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
assert not os.path.lexists(base/'lib/DiophantineConsistency/Norm38ForwardPrefix.olean')
review=D/'reviews/nine-sharing-forward38-draft-independent';r=subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],capture_output=True);assert r.returncode==0 and not r.stderr and r.stdout==(review/'result.json').read_bytes()
print(json.dumps({'status':'PASS_PREFIX_SOURCE_PROVIDER_REVIEW_ONLY','source_sha256':sha(src),'runner_sha256':sha(q/'run.py'),'base_modules':len(s['rows']),'scope':'Source text and provider point checks; no Lean compile, source norm or seed-zero claim.'},indent=2,sort_keys=True))
