#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-mul-zero-native-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='a9eea45cf5870d7116c9384962b4181c8a59726afe83c527957edcbf9340a064' and sha(p/'source-manifest.json')=='5273ff6261075d001e995b2794453dc74ae784e1ae43165a112a42695dd449c2'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMulZeroNative';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMulZeroContext','DiophantineConsistency.IPRANativeAxiomImage'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(φ : Propositionᵢ language) (h : Δ ⊢[𝗜𝗻𝘁¹] φ)','rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl','DefiningEquationI.composition','DefiningEquationI.projection','DefiningEquationI.recursionBase','DefiningEquationI.zero','EqualityAxiomI.substitution','EqualityAxiomI.refl','extended nativeTheory ⊢! equal (mult a mz) mz','contextNative _ (mul_zero a)'):assert z in s
assert s.count('IPRANativeAxiomImage.native_axiom (')==9
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-mul-zero-context-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);f=json.loads(x.stdout);assert f['status']=='PASS' and f['observed']['IPRANativeAxiomImage']['sha256']=='55363675d98f4a7f543b1e771a59cd7c9331fcb0643afbdb57e488a52ad54b71'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed nativeTheory discharge of nine finite-context axioms and open mul-zero proof; numeral normalization and positive leaf separate'},indent=2))
