#!/usr/bin/env python3
"""Review positive-beta seed iff and two-provider union, without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-seed-iff-check';draft=research/'nine-sharing-sign17-seed-iff-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='48d9dead03dc7a59ed728f1b360b780e7bd9664a4931767f7c4f8f4ba9259c70';e,=json.loads(m.read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17SeedExistential.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17SeedExistential' and sha(src)==sha(draft/src.name)==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.Sign17ReverseBridge','DiophantineConsistency.Sign17GapFromSeed']
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) (hb : 0 < beta)' in s and '(∃ v : Fin 18 → V, v 0 = x ∧ InternalZero (SharingSeed17Degree96.seed p) v)' in s and '∃ v : Fin 19 → V, v 0 = x ∧ InternalZero (SharingSeed18Degree94.seed p) v' in s
assert 'Sign17GapFromSeed.exists_gap p beta v hp0 hb hz' in s and 'Sign17ZeroBridge.forward p v gap hg hz' in s and 'Sign17ZeroBridge.backward p v hz' in s and 'simpa [Sign17Coordinate.lift] using hv' in s and 'simpa [Sign17Coordinate.drop] using hv' in s
runner=p/'run.py';assert sha(runner)=='6f87294b5ff004792b2c94a27c59b325ab5ff5d0c9b927ab4dcebca16c47815a';r=runner.read_text();assert "for family in ('gap',):" in r and "for family,module in (('gap','Sign17GapFromSeed'),):" in r and "if local=='Sign17ReverseBridge':" in r and "elif local=='Sign17GapFromSeed':" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
survey=p/'provider-union-survey.py';assert "o['outer_exit_code']==0" in survey.read_text() and 'author_observed_numeric_outer_exit' not in survey.read_text()
for review in ('nine-sharing-sign17-zero-assembly-terminal-independent','nine-sharing-sign17-gap-from-seed-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(x.stdout);assert d['status']=='PASS' and d['producers']['gap']['extra_count']==403 and d['producers']['gap']['overlap_count']==1074
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'gap_extras':403,'gap_overlaps':1074,'scope':'proposed same-input Fin18/Fin19 seed iff under represented positive beta; no Lean theorem or endpoint'},indent=2,sort_keys=True))
