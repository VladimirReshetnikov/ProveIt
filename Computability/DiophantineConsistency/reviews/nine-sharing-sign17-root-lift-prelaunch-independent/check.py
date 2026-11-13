#!/usr/bin/env python3
"""Review generic root-form signed-lift source and provider without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-root-lift-check';draft=research/'nine-sharing-sign17-root-lift-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='c8ce70894a2bdb3b41b0f258458342c06f6af092bc22d0e1c3b6001d5fca39ad';e,=json.loads(m.read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17RootLift.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17RootLift' and sha(src)==sha(draft/src.name)==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.Sign17OrderedGap']
assert all('theorem '+x in s for x in ('root_positive','scale_positive','exists_signed_lift')) and s.count('(hb : 0 < beta)')==3
assert 'def root (beta x1 x9 B C : V) : DiffRing V' in s and '(ι beta) * ((ι x1) + 1) + (ι B) + (ι C)' in s
assert '(hNa :' in s and '∃ gap : V, ι gap = ((ι f)+1)*((ι f)+1)-(ι W)*(ι W)' in s and 'Sign17OrderedGap.difference_nonnegative' in s and 'nonneg_iff.mp hn' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
runner=p/'run.py';assert sha(runner)=='655e36cde261635502429ad7b86b937ef52e675bf5a7732003791c459cd5777b';r=runner.read_text();assert "base['status']=='PASS' and len(base['rows'])==2" in r and "if local=='Sign17OrderedGap':expected_hash=base['rows'][0]['object_sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-signed-lift-lemmas-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'generic root/scale/gap source with beta>0 and arbitrary B,C; no concrete AST binding or Lean bridge'},indent=2,sort_keys=True))
