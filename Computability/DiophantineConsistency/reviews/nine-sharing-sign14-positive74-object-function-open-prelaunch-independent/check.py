#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-function-open-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='da1e2c790aff69dd1b2c5dc5fc37e34a1dceeea2a8ca6561b949fe9f98425d39' and sha(p/'source-manifest.json')=='b461a2932edcee974ca2b581d0dc47901791e75b4b0901c9bb9fad2ae928c020'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectFunctionOpen';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftBase','DiophantineConsistency.IPRAFunctionCongruenceClosed'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(f : language.Func k)','(v : Fin (k+k) → Term language ℕ)','extended nativeTheory ⊢! (Rew.embSubsts v ▹ sourceBody f)','instantiateTheory (T := nativeTheory) (sourceBody f) (Classical.choice (function_native f)) v'):assert z in s
src=(root/'Lean/DiophantineConsistency/IPRAFunctionCongruenceClosed.lean').read_text();assert all(z in src for z in ('def sourceBody {k : ℕ}', 'Semisentenceᵢ language (k+k)','def sourceDirect {k : ℕ}', '∀⁰* sourceBody f','theorem function_native {k : ℕ} (f : language.Func k) : nativeTheory ⊢ sourceDirect f'))
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-shift-base-retry02-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();survey=(p/'framework-survey.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r and 'IPRAFunctionCongruenceClosed' in survey
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed instantiated native arbitrary-arity function congruence body, not normalized matrix or sentence'},indent=2))
