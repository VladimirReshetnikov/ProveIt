#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-multisubst-retry03-check';old=root/'research/nine-sharing-sign14-positive74-object-multisubst-retry02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='50e4f2319984113b5367123a276a1a02b9ca764adb87dbf7d2e47b0275117920' and sha(p/'source-manifest.json')=='a2402b9eb5eddaec6339afeb6dfc7a5713d4c04c07cef5b4f1223e536f6c2733'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMultiSubst';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCoordinateNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
a=a.replace('  apply Classical.choice\n  change extended nativeTheory ⊢ _\n  apply Entailment.FiniteContext.deduct!\n  apply Entailment.FiniteContext.deduct!\n','  apply Entailment.FiniteContext.deduct\'\n  apply Entailment.FiniteContext.deduct\n',1).replace('  exact ⟨(Entailment.FiniteContext.of step) ⨀ he\' ⨀ hb⟩','  exact (Entailment.FiniteContext.of step) ⨀ he\' ⨀ hb',1);assert s==a
prior=(root/'Lean/DiophantineConsistency/IPRANativeAtomStability.lean').read_text();assert "apply Entailment.FiniteContext.deduct'\n    apply Entailment.FiniteContext.deduct" in prior
for f in ('nine-sharing-sign14-positive74-object-multisubst-retry02-failure-independent','nine-sharing-sign14-positive74-object-coordinate-native-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'guarded finite simultaneous substitution retry; hypotheses unchanged'},indent=2))
