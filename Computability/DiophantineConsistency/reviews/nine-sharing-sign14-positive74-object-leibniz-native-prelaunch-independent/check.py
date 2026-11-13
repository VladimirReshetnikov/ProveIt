#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-leibniz-native-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='02a69a01849be78eb192fe56f63a10c08701c06f3b76e22c2bedd899a6186497' and sha(p/'source-manifest.json')=='93d37f66f0d9de34773423d8f016ca690605147c44f0f28ca5f9a2bb0987896b'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectLeibnizNative';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('extended nativeTheory ⊢! (eqAt x y 🡒','((Rew.embSubsts ![x] ▹ φ) 🡒 (Rew.embSubsts ![y] ▹ φ)))','NativeAxiom.equality (EqualityAxiomI.substitution φ)','instantiateTheory (T := nativeTheory) (IPRAAllSpecialize.leibnizBody φ) ha ![x,y]','eqAt, left_rewrite, right_rewrite'):assert z in s
native=(root/'Lean/DiophantineConsistency/IPRANativeTheory.lean').read_text();assert 'def eqSubstitutionI' in native and '(eqLeft φ 🡒 eqRight φ)' in native
inst=(root/'Lean/DiophantineConsistency/IPRATheoryInstantiation.lean').read_text();assert 'extended T ⊢! (Rew.embSubsts v ▹ φ)' in inst
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-leibniz-rewrite-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native-theory proof of one-coordinate open-term equality substitution; full sentence equivalence separate'},indent=2))
