#!/usr/bin/env python3
"""Read-only review of the 91-gate transformed model-zero comparison."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-xq91-candidate';O=P/'observations/model-attempt01';A=P/'observations/algebra-attempt01/terminal.json'
PIN={P/'XQ91Model.lean':'f7400f5eefa3ac75896fce11e42b7ffde8077c1588e7d85816d4a748d765af94',
 P/'MODEL.md':'1eaaab7e8cb55ada3f4316f981c718388551d5ae584986483caeaadd51e793a0',
 P/'run-model.py':'5b13e5fc74c744faa67cf1628d485e3be7fc46becb99ca73788e6132457ee3e4',
 P/'XQ91.lean':'616084961b539e3c8d8a6e01b7e1a576deeef67d9cfb6f779f0c7a8edb846617',
 P/'candidate.json':'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513',
 O/'terminal.json':'bdc4d6cb11c87d0161b0d777f2be050ef6bbf7ca11d6a5ce1b88a345d21ce36b',
 O/'XQ91Model-source.txt':'f7400f5eefa3ac75896fce11e42b7ffde8077c1588e7d85816d4a748d765af94',
 O/'stdout':'052087cad4162c3cfd424cb1101c1fe39d8a3ec178b8e2e4f1eb0b4c6288e0af',
 A:'647ab4935265c9db60a9f6b4975f3eb48bc14426b2d102fc10c969730232db6a'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch '+str(p))
s=(P/'XQ91Model.lean').read_text();r=json.loads((O/'terminal.json').read_text());a=json.loads(A.read_text())
need(s.splitlines()[0]=='import XQ91','wrong direct import')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model assumptions mismatch')
need('def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)' in s,'natural port cast mismatch')
transform=('def transform (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=\n'
           '  Function.update v 5 ((1 + v 0 * (p 0 : V)) * v 5)')
need(transform in s,'X=q*w transform mismatch')
statement=('theorem zero_iff_transformed (p : Fin 4 → ℕ) (v : Fin 12 → V) :\n'
           '    InternalZero (graph (integerPorts p)).output v ↔\n'
           '      InternalZero (FreeJQCube92.graph (integerPorts p)).output (transform p v) := by')
need(statement in s,'exact transformed zero theorem mismatch')
for marker in ('internalZero_iff','rw [internalZero_iff, internalZero_iff, lift_cast, hout, hout\']',
               'Expr.evalRing_add, Expr.evalRing_mul',
               'rw [FreeJXQ91.first_eval, FreeJXQ91.main_eval, FreeJXQ91.ordinary_eval]'):
 need(marker in s,'missing proof step '+marker)
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-xq91-algebra-independent/check.py')],capture_output=True,check=True)
need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','prior algebra and graph audit failed')
need(r['exit']==0 and r['reason'] is None and r['before']==r['after'] and r['selected_provider_unchanged'],'failed model run')
for path,h in r['before'].items():need(Path(path).is_file() and sha(path)==h,'direct input drift '+path)
expected="'FreeJXQ91Model.lift_cast' depends on axioms: [propext, Classical.choice, Quot.sound]\n'FreeJXQ91Model.zero_iff_transformed' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need((O/'stdout').read_text()==expected and not (O/'stderr').read_bytes(),'unexpected axiom report')
need(sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'log hash mismatch')
cmd=r['command'];out=Path(cmd[cmd.index('-o')+1]);compiled=Path(cmd[cmd.index('-o')-1])
need(sha(out)==r['object_sha256']=='ae968c1b57af60e8654c3ff243059f18106d4b9c94a2260c71d19176fa79d8ec','model object drift')
need(sha(compiled)==PIN[P/'XQ91Model.lean'],'compiled source drift')
need(len(r['samples'])==2 and min(x['mem_available_kib'] for x in r['samples'])==18256628 and max(len(x['lean']) for x in r['samples'])==2,'resource sample mismatch')
paths=r['lean_path'].split(':');need(paths[1:]==a['lean_path'].split(':'),'algebra provider order changed');provider={}
for root in paths[:-1]:
 for p in sorted(Path(root).rglob('*.olean')):
  need(p.is_file(),'missing selected object');provider[str(p)]={'sha256':sha(p),'realpath':str(p.resolve())}
need(provider==r['selected_provider_before'] and len(provider)==76,'model selected provider drift')
need(a['exit']==0 and a['reason'] is None and a['selected_provider_unchanged'] and a['before']==a['after'],'algebra receipt failed')
need(a['selected_provider_before'].items()<=provider.items(),'prior algebra provider changed')
direct=Path(paths[0])/'XQ91.olean';need(str(direct) in provider and provider[str(direct)]['sha256']==a['object_sha256'],'algebra object mismatch')
for p,h in PIN.items():need(sha(p)==h,'input changed during review '+str(p))
for path,info in provider.items():need(sha(path)==info['sha256'] and str(Path(path).resolve())==info['realpath'],'provider changed during review '+path)
need(sha(out)==r['object_sha256'],'object changed during review')
print(json.dumps({'status':'PASS','model_attempt_exit':r['exit'],'provider_files_rehashed':len(provider),
 'prior_algebra_object_matches':True,'prior_algebra_and_graph_review':'PASS',
 'scope':'zero equivalence only at X=q*w transformed valuation','model_object_sha256':r['object_sha256']},indent=2))
