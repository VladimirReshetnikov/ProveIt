import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-carrier-retry02';old=R/'nine-sharing-norm38-static-carrier-retry01';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';man=q/'source-manifest.json';src=q/'src/DiophantineConsistency/Norm38StaticCarrierConditional.lean';orig=old/'src/DiophantineConsistency/Norm38StaticCarrierConditional.lean'
assert sha(src)=='e6a802d24f38d6eec6193b96ff815b9845465e7f2049aab48d71ff14aa70a011' and sha(man)=='377a9566c2fa5ffc02611250792cb3fc51ad7e78207645d4965ff7b8662648bb' and sha(run)=='8f88b405f71eb6774452e419fd56e1250b03360dcad6231bcc8258c9a972c1c6'
assert sha(orig)=='13c7a4433cf5deac75fe279e70c816f093de875f4c05af90f1c925d98bd4ed6c';a=orig.read_text();assert a.count('one_mul,sub_self]')==1 and a.replace('one_mul,sub_self]','one_mul,_root_.sub_self]')==src.read_text()
a=(old/'run.py').read_text().replace('static-carrier-retry01-20261105','static-carrier-retry02-20261105').replace('6dd77a2333268b3739856bbc405ca639dfc0ae2e5a8eeeac4ee3f04e99ce53d8',sha(man));assert a==run.read_text()
assert sha(q/'field_preflight.py')==sha(old/'field_preflight.py')=='4874dede3ed41c8502933a6b2b9a4303557ea203ef13a58a52f18888235e32f4'
f=old/'attempt01';assert sha(f/'state.json')=='36522d2c3ecc5be94735b41e9a45be77569c71f1da80d10da87c78f13d919f27';state=json.loads((f/'state.json').read_text());assert state['status']=='FAILED' and state['rows'][0]['compile']['exit']==1 and state['rows'][0]['compile']['stop_reason'] is None
log=(f/'Norm38StaticCarrierConditional-compile.txt').read_text();assert sha(f/'Norm38StaticCarrierConditional-compile.txt')=='c9bde5cfbdb833eb4e1df8181d8855af30eb1763237decf10ede2be3b30b8f53' and 'error: Ambiguous term' in log and 'sub_self' in log and 'sorryAx' in log
m=json.loads(man.read_text())['rows'];assert len(m)==1 and m[0]['source_sha256']==sha(src) and m[0]['imports']==['DiophantineConsistency.Norm38ReferenceFieldsAll']
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
p=D/'reviews/nine-sharing-norm38-reference-fields-combine-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','source_sha256':sha(src),'runner_sha256':sha(run),'scope':'No Lean replay; conditional theorem and resource fit remain untested.'},indent=2,sort_keys=True))
