#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-close-bind-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='4fbcca699c28b992bdbab5da802849a8b2f7e618d3ccc2d4b24a2d7358fcb71d' and sha(p/'source-manifest.json')=='d32dc8f13f5d59a353ab57f9a515289f66fba284af0c6650badda60457ad5915'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCloseBind';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftToPositiveOpen'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('def freeVec : Fin 14 → Term language ℕ := fun i => &i.val','(Rew.fixitr 0 14).comp (Rew.embSubsts freeVec)','(Rew.emb : Rew language Empty 14 ℕ 14)','i.isLt','∀⁰* (Rew.fixitr 0 14 ▹ (Rew.embSubsts freeVec ▹ φ))','Rewriting.emb (∀⁰* φ)'):assert z in s
old=(root/'research/nine-sharing-sign14-positive74-object-close-bind-check/src/DiophantineConsistency/Sign14Positive74ObjectCloseBind.lean').read_text();assert old.replace('  · simp [Rew.comp_app, freeVec, Rew.fixitr_fvar, Rew.emb_bvar, i.isLt]','  · change (Rew.fixitr 0 14) (&i.val : SyntacticTerm language) = #i\n    rw [Rew.fixitr_fvar, dif_pos i.isLt]\n    congr 1\n    apply Fin.ext\n    rfl')==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-close-bind-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-shift-to-positive-open-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed canonical 14-coordinate rewrite composition and universal closure syntax identity; native closed implications separate'},indent=2))
