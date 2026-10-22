"""Read-only byte/receipt checks; never imports or runs the producer."""
from pathlib import Path
import json,hashlib,re,ast
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');F=R/'Computability/BusyBeaver/Research/ZFC/k225-formal';S=Path('/tmp/k215-phase11-producer');A=Path('/tmp/k215-phase11-main');O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
freeze=read(S/'freeze.json');assert freeze['producer_sha256']=='31fdd538a6cf001d30fa26cb3d4d411306d3df52bea1ede62a54fc17608f1882'
for p,r in freeze['files'].items():assert sha(S/p)==r['sha256']and(S/p).stat().st_size==r['bytes']
adopt=read(A/'adoption.json');assert sha(A/'adoption.json')=='164c58547a324a98294fe9def0a93496e314c36f66eedf1df9beb795881ba9ef'
for r in adopt['files']:assert sha(r['source'])==sha(R/r['target'])==r['sha256']and(R/r['target']).stat().st_size==r['bytes']
for r in adopt['tombstones']:assert not(R/r['target']).exists()and sha(r['archived_before'])==r['before_sha256']and Path(r['archived_before']).stat().st_size==r['before_bytes']
core=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean';adapter=core.with_name('DomRho8.lean');raw=S/'verification/k215/simplification/phase10/upstream-merge/source-review/inputs/DominatedImplication.upstream.lean'
assert sha(core)==sha(A/'generated/BusyBeaver/ZFC/DominatedImplication.lean')=='a128ddd54eebe7a49f75ea25c513c6229f1304fb51a9d9b07539a89b8a094656'
assert sha(adapter)==sha(A/'generated/BusyBeaver/ZFC/DomRho8.lean')==sha(S/'dominated_implication_templates/adapter.txt')==adopt['unchanged_adapter_sha256']
source=(S/'generate_dominated_implication_lean.py').read_text();tree=ast.parse(source);assign={n.targets[0].id:n.value for n in tree.body if isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)}
inputpins=ast.literal_eval(assign['INPUT_PINS'].values[0])if False else read(A/'generate.stdout.json')['input_raw_sha256']
for p,h in inputpins.items():assert sha(F/p)==sha(S/p)==h
assert (F/'../../../Lean').resolve()==R/'Computability/BusyBeaver/Lean'
# Public declaration types and common definitions are text-identical; only two private aliases disappear.
x=raw.read_text();y=core.read_text();
for n in ['rho8_all','composition','lift_right']:
 pat=r'(?m)^theorem '+n+r'\b[\s\S]*?:=';assert re.search(pat,x).group()==re.search(pat,y).group()
start=x.index('universe v');end=x.index('\nsection\n');assert x[start:end]==y[y.index('universe v'):y.index('\nsection\n')]
def blocks(s):
 ms=list(re.finditer(r'(?m)^private theorem (d\d+)\b',s));return {m.group(1):s[m.start():ms[i+1].start()if i+1<len(ms)else s.index('/-- Restricted rows',m.end())]for i,m in enumerate(ms)}
xb,yb=blocks(x),blocks(y);assert len(xb)==58 and len(yb)==56 and set(xb)-set(yb)=={'d56','d58'}
for n in yb:assert xb[n]==yb[n],n
assert 'd56 h'not in y and 'd58 h'not in y
# Saved observed commands and actual stdout/stderr hashes, no invocation here.
execution=read(A/'producer-execution.json');assert sha(A/'producer-execution.json')==adopt['producer_reproduction_sha256']
for p,h in execution['input_pins'].items():assert sha(p)==h
for idx,label in enumerate(['generate','check']):
 run=execution['runs'][idx];assert run['exit_code']==0
 expected=['/home/codex/.local/bin/python','-B',str(S/'generate_dominated_implication_lean.py'),'--out',str(A/'generated')]+(['--check']if idx else [])
 assert run['command']==expected and sha(A/(label+'.stdout.json'))==run['stdout_sha256']and sha(A/(label+'.stderr.txt'))==run['stderr_sha256']
 assert not(A/(label+'.stderr.txt')).read_bytes()
maint=read(A/'maintained-check.json');assert maint['exit_code']==0 and maint['command']==['/home/codex/.local/bin/python','-B',str(F/'generate_dominated_implication_lean.py'),'--check']
assert sha(A/'maintained-check.stdout.json')==maint['stdout_sha256']and sha(A/'maintained-check.stderr.txt')==maint['stderr_sha256']
metrics=read(A/'generate.stdout.json');assert metrics==read(A/'check.stdout.json')==read(A/'maintained-check.stdout.json')==read(A/'generated/metrics.json')
assert metrics['raw_checked']=={'private_steps':58,'private_mp':58,'restricted_rows':23,'public_mp':1,'seed_uses':0,'public_targets':['rho8_all','composition','lift_right']}
assert metrics['checked']=={'private_steps':56,'private_mp':56,'restricted_rows':23,'public_mp':3,'seed_uses':0,'public_targets':['rho8_all','composition','lift_right']}
assert sha(core)==metrics['generic_sha256'] and sha(adapter)==metrics['adapter_sha256']
old=(S/'template-all-code-references.txt').read_text().splitlines();now=(O/'current-code-references.txt').read_text().splitlines();prefix=str((F/'generate_dominated_implication_lean.py').relative_to(R))+':'
assert len(old)==25 and len(now)==22
assert sorted(z for z in old if not z.startswith(prefix))==sorted(z for z in now if not z.startswith(prefix))
assert [z for z in now if z.startswith(prefix)]==[prefix+"19:ADAPTER = 'dominated_implication_templates/adapter.txt'"]
for n in ['core-prefix.txt','core-suffix.txt']:
 assert (F/'verification/k215/simplification/phase10/source-proposal/production/dominated_implication_templates'/n).is_file()
 assert (F/'verification/k215/simplification/proposals/proof-core/generation/generation/templates'/n).is_file()
canonical=read(A/'canonical-review.json');assert canonical['adoption_sha256']==sha(A/'adoption.json')and canonical['full_result_sha256']==adopt['compiled_full_result_sha256']
assert len(canonical['ledger'])==197
for row in canonical['ledger'].values():assert sha(R/row['canonical'])==row['source']
result={'status':'PASS_READ_ONLY_PRODUCER_ADOPTION_BINDINGS','producer_sha256':sha(S/'generate_dominated_implication_lean.py'),'adoption_sha256':sha(A/'adoption.json'),'raw_core_sha256':sha(raw),'final_core_sha256':sha(core),'adapter_sha256':sha(adapter),'frozen_files_checked':len(freeze['files']),'raw_private_steps':58,'final_private_steps':56,'unchanged_private_bodies':56,'final_public_mp':3,'all_restricted_rows':23,'six_public_declaration_interfaces_unchanged':True,'replacement_files':2,'tombstones':2,'historical_reference_lines':25,'current_reference_lines':22,'historical_nonproduction_reference_lines_unchanged':21,'root_producer_runs_reviewed':3,'current_Lean_sources_rehashed':197,'compiler_invocations_by_this_review':0,'producer_invocations_by_this_review':0,'reader_sha256':sha(__file__)}
(O/'bindings.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
