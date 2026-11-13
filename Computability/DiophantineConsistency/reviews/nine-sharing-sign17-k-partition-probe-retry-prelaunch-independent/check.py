#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-partition-probe-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='7f60e86bac83cf43c7740da50c5e950cad2ac369d4fc8e3231db0504f6a38b9b' and sha(p/'source-manifest.json')=='a0cc5f2f079ac94caf57d39965f94493b25c3759356eaa0ec32824c4e89cf588'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KPartitionProbe.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KPartitionProbe' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign17-k-partition-probe-check/src/DiophantineConsistency/Sign17KPartitionProbe.lean').read_text();assert old.replace('simpa [Fin.natAdd, Nat.add_assoc] using h2 k','simpa only [Fin.natAdd, ← Nat.add_assoc, Nat.reduceAdd] using h2 k')==s
for t in ('theorem split_three (P : Fin 9 → Prop)','h0 : ∀ i : Fin 2, P (i.castAdd 7)','h1 : ∀ i : Fin 3, P ((Fin.natAdd 2 i).castAdd 4)','h2 : ∀ i : Fin 4, P (Fin.natAdd 5 i)','∀ i, P i','Fin.addCases (m := 2) (n := 7)','Fin.addCases (m := 3) (n := 4)'):assert t in s
assert list(range(2))+list(range(2,5))+list(range(5,9))==list(range(9))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent','nine-sharing-sign17-k-partition-probe-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic Fin9 predicate partition into blocks 2+3+4; not global rank/K/file'},indent=2))
