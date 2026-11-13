#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-95gate-lean-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='56a2145678fe5294e940101bf868e1ef22ba914a41958c028afdd9b9ce684464' and sha(p/'source-manifest.json')=='e9a88f0b241fe5b685de5b62db3fa5c430c17cc1e2aed9fe29d27cafb93f6d4f'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized95.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized95' and e['imports']==['DiophantineConsistency.Sign14AbstractExpressionDef','DiophantineConsistency.ModelJonesSyntax'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign14-95gate-lean-draft/Sign14Optimized95.lean').read_text();old=old.replace('Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,\n    Int.cast_one]','Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_ofNat, Expr.evalRing_var,\n    Int.cast_one, Nat.cast_one]').replace('Expr.evalRing_constant, Expr.evalRing_var, Int.cast_one]','Expr.evalRing_constant, Expr.evalRing_ofNat, Expr.evalRing_var, Int.cast_one, Nat.cast_one]');assert old==s
for f in ('nine-sharing-sign14-95gate-lean-draft-independent','nine-sharing-sign14-95gate-candidate-independent','nine-sharing-sign14-readable-lean-probe-terminal-independent','nine-sharing-sign14-prefix-dag-assembly-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-prefix-dag-assembly-check-20261110/lib/DiophantineConsistency');pins={'Sign14AbstractExpressionDef':('8cf256a30987633bba738449290b463e7082869d2e69456982006b59b9813c54','/tmp/nine-sharing-sign14-expression-eval-check-20261110/lib/DiophantineConsistency/Sign14AbstractExpressionDef.olean'),'ModelJonesSyntax':('ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171','/tmp/nine-light-jones-probe-20261105/lib/DiophantineConsistency/ModelJonesSyntax.olean')}
for n,(h,path) in pins.items():z=base/(n+'.olean');assert z.is_symlink() and str(z.resolve())==path and sha(z)==h
# Trace the recorded direct imports of both direct providers to available overlay targets.
st=json.loads((root/'research/nine-sharing-sign14-expression-eval-check/attempt01/state.json').read_text());r=st['rows'][0]
for mod,d in r['dependencies'].items():
 if mod=='Init':continue
 z=base/(mod.split('.')[-1]+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256']
for n in ('ExecutableJonesCore','WeightedExpressionDegree'):
 z=base/(n+'.olean');assert z.is_file() and z.resolve().is_file()
assert 'ExecutableJonesCore.olean' in Path('/tmp/nine-light-jones-probe-20261105/ModelJonesSyntax-deps.txt').read_text() and 'WeightedExpressionDegree.olean' in Path('/tmp/nine-light-jones-probe-20261105/ModelJonesSyntax-deps.txt').read_text()
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic CommRing optimized seed evaluation equality only, conditional on Lean; no AST/JSON/PDF/degree/iPRA Lean theorem'},indent=2))
