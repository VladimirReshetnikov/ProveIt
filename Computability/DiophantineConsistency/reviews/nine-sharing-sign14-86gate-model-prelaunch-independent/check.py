#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-86gate-model-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='58a08fc5a38c84218a35d0eaf624ab350bb81a3dc1ee372d895975fa86583623' and sha(p/'source-manifest.json')=='ffc44379068271cae1d6db84e1f15f3af6ef0ca23623085df4d92af379a120d9'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized86Model.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized86Model' and e['imports']==['DiophantineConsistency.Sign14Optimized86To92'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','theorem zero_iff (p : Fin 4 → ℤ) (w : Fin 14 → V)','InternalZero (Sign14Optimized86Expression.expression p) w','InternalZero (Sign32GenericRemoveInput.removeInput (Sign14Optimized92.seed p)) w','[internalZero_iff, Sign14Optimized86To92.eval_expression]','theorem zero_exists_iff (p : Fin 4 → ℤ)','exists_congr (zero_iff p)'):assert t in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-86gate-to92-expression-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'pointwise/existential model-zero equivalence, arbitrary ports, conditional on Lean; degree/iPRA/JSON/PDF separate'},indent=2))
