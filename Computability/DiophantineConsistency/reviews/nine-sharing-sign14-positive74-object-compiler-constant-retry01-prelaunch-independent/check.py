#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-compiler-constant-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='7081ded01dc19a0f2ece72a0b870a36b20238e52179d078093c05e9b80941500' and sha(p/'source-manifest.json')=='8d54154ddaaf2934ad045f5fc5fa15e845dd0060978ea08a2c9e61676e87a40b'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCompilerConstant';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftNegativeLeaf'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(h : ∀ i, ¬ SetTheory.PA.Term.Free i t)','reflectedOpen t v = reflectedOpen t w','induction t with','| var i =>','| zero =>','| succ t ih =>','| add p q hp hq =>','| mul p q hp hq =>','compiledOpen (.constant k) v = compiledOpen (.constant k) w','ArithmeticExpression.binaryNumeral_closed k i'):assert z in s
old=(root/'research/nine-sharing-sign14-positive74-object-compiler-constant-check/src/DiophantineConsistency/Sign14Positive74ObjectCompilerConstant.lean').read_text();assert old.replace('induction t generalizing h with','induction t with')==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-compiler-constant-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-shift-negative-leaf-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed assignment independence of compiled closed terms and constants; native reflexivity, positive leaf and closure separate'},indent=2))
