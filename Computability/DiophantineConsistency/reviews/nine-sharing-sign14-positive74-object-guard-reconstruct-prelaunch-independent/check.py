#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-guard-reconstruct-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='fca626e173328811f2e00a9f6ab76790d22f8fe7503e39b9cde9273eac490c88' and sha(p/'source-manifest.json')=='099f03a6f9574f8e089900d472e6d49a4a6532c5eedf87975334f24ba87d70c1'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectGuardReconstruct';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectPredecessor'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='d70d91f580004710ce121636ccf367c3233384245288ee8c5c96dee9b0e28232' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(h : ∀ i, extended nativeTheory ⊢! (a i 🡒 b i))','((⋀ (xs.map a)) 🡒 (⋀ (xs.map b)))','| [] =>','| [x] =>','| x :: y :: xs =>','mapConjImp a b h (y :: xs)','int_prover','(List.finRange 14).map fun i => ∼eqAt (v i) zero','(List.finRange 14).map fun i => eqAt (v i) (succ (pred (v i)))','nonzeroGuardOpen v 🡒 reconstructGuardOpen v','nonzeroReconstructionOpen (v i)'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-predecessor-retry02-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'14-coordinate open conjunction reconstruction only; closed guard/term substitution/endpoint separate'},indent=2))
