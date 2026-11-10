#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-degree-subst-bound-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d8a8e2f19b2be9bf4859c5598b426522ca7e904174bfe85745cf39c75fd9c1eb' and sha(p/'source-manifest.json')=='f02780cbe22b9d6c4495994aea081a6c8d07a6e2fba3aecc1be1d170309197ef'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74DegreeSubstBound';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectEndpoint'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('{σ : Type*} (p : MvPolynomial σ ℤ)','(g : σ → MvPolynomial σ ℤ) (hg : ∀ i, (g i).totalDegree ≤ 1)','(MvPolynomial.eval₂ MvPolynomial.C g p).totalDegree ≤ p.totalDegree','MvPolynomial.totalDegree_finsetSum_le','MvPolynomial.totalDegree_finsetProd','MvPolynomial.totalDegree_pow','MvPolynomial.le_totalDegree hd'):assert z in s
old=(root/'research/nine-sharing-sign14-positive74-degree-subst-bound-check/src/DiophantineConsistency/Sign14Positive74DegreeSubstBound.lean').read_text();assert old.replace('    _ ≤ 0 + ∑ i ∈ d.support, d i := by simpa using hp\n    _ = d.sum (fun _ e => e) := rfl','    _ ≤ 0 + ∑ i ∈ d.support, d i := by\n      simpa only [MvPolynomial.totalDegree_C, zero_add] using hp\n    _ = d.sum (fun _ e => e) := by simp [Finsupp.sum]')==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-degree-subst-bound-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-endpoint-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic same-index degree≤1 substitution upper bound; invertibility and candidate degree separate'},indent=2))
