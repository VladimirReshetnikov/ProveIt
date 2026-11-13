#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-function-binary-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='49d13070cb3d8468f7b5e5688b2702c61072287da3941cfe76bb0a3a2ab48ebe' and sha(p/'source-manifest.json')=='1f8ac28c842f47b7342e27a8209443e73441078daa575a7dd66202269e59f711'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectFunctionBinary';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectFunctionOpen'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Rew.embSubsts ![a,b,c,d] ▹ sourceBody f','eqAt a c ⋏ (eqAt b d ⋏ ⊤)','eqAt (.func f ![a,b]) (.func f ![c,d])','simpa only [binary_body] using functionOpen f ![a,b,c,d]'):assert z in s
src=(root/'Lean/DiophantineConsistency/IPRAFunctionCongruenceClosed.lean').read_text();assert '![#(i.castAdd k), #(i.addNat k)]' in src
# k=2 makes the left pair indices 0,1 and right pair 2,3.
assert [(i,i+2) for i in range(2)]==[(0,2),(1,3)]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-function-open-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed binary congruence normalized to (a=c ∧ b=d ∧ true) → f(a,b)=f(c,d)'},indent=2))
