#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-close-imp-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='281f5f5beb68c1e309392c1fdf72463cb316249126d1298d37455d7428931e8e' and sha(p/'source-manifest.json')=='8298691b0a61f4b1863ee0879cf4ebfa45b71bafde2142cfb36297cc1cb11481'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCloseImp';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCloseBind'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(hΓ : Γ⁺ = Γ)','HilbertProofᵢ.geNOverFiniteContext','(σ : Sentenceᵢ language) (φ : Semisentenceᵢ language 14)','(h : extended nativeTheory ⊢! (Rewriting.emb σ 🡒 (Rew.embSubsts freeVec ▹ φ)))','nativeTheory ⊢! (σ 🡒 ∀⁰* φ)','Rewriting.rew_emb_eq_emb','closeContext [P] hshift hc 14','bindSentence14 φ','extendedToTheory (T := nativeTheory)'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-close-bind-retry02-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic closed-antecedent closure of actual open native implication; specific equivalence separate'},indent=2))
