#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-multisubst-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='396c16be1f67d28cf17969da1c20827ae8cd08206c2a078e295beee037733935' and sha(p/'source-manifest.json')=='4ef28bc904719e5476eafc7f24c0fd63b3ca8268f1fe538f3965c9d0c3701892'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMultiSubst';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(h : ∀ i, extended nativeTheory ⊢! (guard 🡒 eqAt (v i) (w i)))','extended nativeTheory ⊢! (guard 🡒 ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts w ▹ φ)))','mix ∅ v w = v','mix Finset.univ v w = w','induction s using Finset.induction_on','simpa [mix, hi] using h i','updateOpen φ (mix s v w) i (w i)','simpa only [mix_insert]'):assert z in s
src=(root/'Lean/DiophantineConsistency/IPRAFunctionCongruenceOpen.lean').read_text();assert 'if j ∈ s then w j else v j' in src and 'mix (insert i s) v w = update i (w i) (mix s v w)' in src and 'fun j => if j = i then x else v j' in src
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-coordinate-native-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed guarded finite simultaneous substitution under explicit coordinate equalities; full sentence separate'},indent=2))
