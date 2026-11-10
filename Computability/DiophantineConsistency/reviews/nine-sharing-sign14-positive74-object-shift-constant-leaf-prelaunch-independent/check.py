#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-constant-leaf-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='1ee9425273467a5900321845ef6e33c29f0d3e5b59cb53c124f750058df428ee' and sha(p/'source-manifest.json')=='523955024a4684fe6ec0c95caf5eb4fe459291a1712fe8470c4b8d2a0867f045'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftConstantLeaf';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCompilerConstant','DiophantineConsistency.IPRAStandardTheory','DiophantineConsistency.IPRANativeAxiomImage'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('eqAt (compiledOpen (.constant k) v) (compiledOpen (.constant k) w)','IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)','rw [← compiled_constant k v w]','IPRAStandardTheory.eqReflAt hrefl (compiledOpen (.constant k) v)'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-compiler-constant-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);f=json.loads(x.stdout);assert f['status']=='PASS' and f['observed']['IPRANativeAxiomImage']['sha256']=='55363675d98f4a7f543b1e771a59cd7c9331fcb0643afbdb57e488a52ad54b71' and 'IPRAStandardTheory' in f['observed']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native constant leaf from compiler independence and equality reflexivity; positive leaf and closure separate'},indent=2))
