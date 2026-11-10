#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-matrix-guard-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6261719ca6308bc9c7d86ca21d18a61196e53543e02d60972aec9072ef7accad' and sha(p/'source-manifest.json')=='55bd92ce60c7177c5630513915c858c5b7c1a46b098471c1abea0efcf1a5ad22'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMatrixGuard';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectGuardedSubst'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('e.splitNatural.1','e.splitNatural.2','Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val','(Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard) 🡒','∼(Rew.embSubsts (predSuccVec v) ▹ equalityMatrix e) 🡒','∼(Rew.embSubsts v ▹ equalityMatrix e)','Entailment.C_trans (guardedSubstitution (equalityMatrix e) v) Entailment.CCCNN'):assert z in s
old=(root/'research/nine-sharing-sign14-positive74-object-guard-check/src/DiophantineConsistency/Sign14Positive74ObjectGuard.lean').read_text();assert all(z in old for z in ('sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)','sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2)','guard 🡒 ∼(Semiformulaᵢ.rel Language.ORing.Rel.eq'))
for f in ('nine-sharing-sign14-positive74-object-guarded-subst-terminal-independent','nine-sharing-sign14-positive74-object-guard-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed intuitionistic guarded contrapositive on unshifted splitNatural equality matrix'},indent=2))
