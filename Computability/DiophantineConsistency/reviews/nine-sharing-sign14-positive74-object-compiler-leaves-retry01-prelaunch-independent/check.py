#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-compiler-leaves-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='028e7abfd2aa4d72dd4f7b0b46bc108793c1bb785613c8990a44f00af8cbb12f' and sha(p/'source-manifest.json')=='7b3830ebb045c2e78f6a3ad485a604746acbb30eb31a51d1780f7e782da6f588'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCompilerLeaves';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftInduction'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('compiledOpen (.var i) v = v i','compiledOpen (.constant 0) v = zero','compiledOpen (.constant 1) v =','.func addCode ![.func mulCode ![.func addCode ![.func addCode ![zero,one],one],zero],one]') : assert z in s
old=(root/'research/nine-sharing-sign14-positive74-object-compiler-leaves-check/src/DiophantineConsistency/Sign14Positive74ObjectCompilerLeaves.lean').read_text()
old=old.replace('    sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func, embedding, zero]\n\ntheorem compiled_one','    sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func, embedding, zero]\n  constructor\n  · rfl\n  · funext i\n    exact Fin.elim0 i\n\ntheorem compiled_one')
old=old.replace('Function.comp_def, funext_iff, Fin.forall_fin_two] <;> rfl',"Function.comp_def, funext_iff, Fin.forall_fin_two] <;> (repeat' constructor)")
assert old==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-compiler-leaves-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-shift-induction-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed variable, zero and one compiler shape equalities; native arithmetic normalization and leaf proofs separate'},indent=2))
