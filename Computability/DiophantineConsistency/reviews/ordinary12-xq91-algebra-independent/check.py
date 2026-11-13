#!/usr/bin/env python3
"""Read-only review of the 91-gate algebra theorem and recorded build."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-xq91-candidate';O=P/'observations/algebra-attempt01'
Q=D/'research/ordinary12-qcube92-candidate/observations/attempt05/terminal.json'
PIN={P/'XQ91.lean':'616084961b539e3c8d8a6e01b7e1a576deeef67d9cfb6f779f0c7a8edb846617',
 P/'ALGEBRA.md':'4d1242ac5ae6c697c7c214de11c9ad31b043305d3187e8085c7e0542f5614f86',
 P/'run.py':'35d328a1bfa28cf733ea708c84456af38ee51d4679f38af19dbd6fee031f0d46',
 P/'candidate.json':'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513',
 P/'check_lean_graph.py':'b1c658e930aad6fa5392412eecc6295cc2994475d394c748fd31baf45c36772f',
 P/'check_graph.py':'f6fa959216fdf8fb1be0e831e71ed9ecbd1f648c1b36e036b13dc8e1fd6b3191',
 O/'terminal.json':'647ab4935265c9db60a9f6b4975f3eb48bc14426b2d102fc10c969730232db6a',
 O/'XQ91-source.txt':'616084961b539e3c8d8a6e01b7e1a576deeef67d9cfb6f779f0c7a8edb846617',
 O/'stdout':'56b88b5c450307910dd19533024d6700fabbd50cfa142259cefafe433aeb7de1',
 P/'observations/graph01/stdout':'0fb7551e5732f1375bdf1e5f7ab43eb8dd92639ef92d9cd0da7ac0762e48a70d',
 Q:'aaf66f7a256fb37d8412a8b92e595314ff42c097a5c83af0fbcf421f587f6d59'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'pin mismatch '+str(p))
s=(P/'XQ91.lean').read_text();g=json.loads((P/'candidate.json').read_text());r=json.loads((O/'terminal.json').read_text());prior=json.loads(Q.read_text())
need(s.splitlines()[0]=='import QCube92','wrong import')
start='def graph (p : Fin 4 → ℤ) : Graph :=\n';need(s.count(start)==1,'graph declaration')
actual=s.split(start,1)[1].split('\nvariable {R',1)[0].splitlines()
expected=[]
for i,n in enumerate(g['witnesses']):expected.append(f'  let {n} : Expr (Fin 12) := .var {i}')
for i,n in enumerate(g['fixed_numerals']):expected.append(f'  let {n} : Expr (Fin 12) := .constant (p {i})')
for n,op,x,y in g['source']:expected.append(f'  let {n} := {x} {op} {y}')
expected.append('  ⟨A0, A1, N, P12⟩')
need(actual==expected and len(g['source'])==91,'source/JSON graph mismatch')
need('structure Graph where\n  first : Expr (Fin 12)\n  main : Expr (Fin 12)\n  ordinary : Expr (Fin 12)\n  output : Expr (Fin 12)' in s,'wrong projections')
need('variable {R : Type*} [CommRing R]' in s and 'Function.update v 5 ((1 + v 0 * (p 0 : R)) * v 5)' in s,'ring or lift mismatch')
for name in ('first','main','ordinary'):
 st=(f'theorem {name}_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :\n'
     f'    (FreeJQCube92.graph p).{name}.evalRing (liftX p v) = (graph p).{name}.evalRing v := by')
 need(st in s,'ring theorem statement mismatch: '+name)
for name in ('factor_bt','factor_main'):need('theorem '+name in s,'missing factor theorem')
# Rerun separate external graph checks; no Lean invocation.
for name in ('check_lean_graph','check_graph'):
 x=subprocess.run([sys.executable,'-I','-S','-B',str(P/(name+'.py'))],capture_output=True,check=True)
 need(not x.stderr and json.loads(x.stdout)['status']=='PASS','author graph checker failed '+name)
 if name=='check_lean_graph':need(x.stdout==(P/'observations/graph01/stdout').read_bytes(),'captured graph output differs')
 opt=subprocess.run([sys.executable,'-I','-S','-B','-O',str(P/(name+'.py'))],capture_output=True,text=True)
 need(opt.returncode!=0 and 'optimized python' in opt.stderr.lower(),'optimized checker not refused')
independent=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-xq91-independent/check.py')],capture_output=True,check=True)
need(not independent.stderr and json.loads(independent.stdout)['new_live_operations']==91,'prior 91 graph audit failed')
need(r['exit']==0 and r['reason'] is None and r['before']==r['after'] and r['selected_provider_unchanged'],'failed author run')
for path,h in r['before'].items():need(Path(path).is_file() and sha(path)==h,'recorded direct input drift '+path)
expected_log=("'FreeJXQ91.first_eval' depends on axioms: [propext, Quot.sound]\n"
 "'FreeJXQ91.main_eval' depends on axioms: [propext]\n"
 "'FreeJXQ91.ordinary_eval' depends on axioms: [propext]\n")
need((O/'stdout').read_text()==expected_log and not (O/'stderr').read_bytes(),'unexpected axiom reports')
need(sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'log hash drift')
cmd=r['command'];out=Path(cmd[cmd.index('-o')+1]);compiled=Path(cmd[cmd.index('-o')-1])
need(sha(out)==r['object_sha256']=='747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d','object hash drift')
need(sha(compiled)==PIN[P/'XQ91.lean'],'compiled source drift')
need(len(r['samples'])==2 and min(x['mem_available_kib'] for x in r['samples'])==18257092 and max(len(x['lean']) for x in r['samples'])==2,'resource sample mismatch')
paths=r['lean_path'].split(':');provider={}
for root in paths[:-1]:
 for p in sorted(Path(root).rglob('*.olean')):
  need(p.is_file(),'missing provider');provider[str(p)]={'sha256':sha(p),'realpath':str(p.resolve())}
need(provider==r['selected_provider_before'] and len(provider)==75,'selected provider drift')
need(prior['exit']==0 and prior['reason'] is None and prior['selected_provider_unchanged'] and prior['before']==prior['after'],'prior 92 algebra receipt failed')
need(prior['selected_provider_before'].items()<=provider.items(),'92 selected provider mismatch')
direct=Path(paths[0])/'QCube92.olean'
need(str(direct) in provider and provider[str(direct)]['sha256']==prior['object_sha256'],'92 imported object mismatch')
for p,h in PIN.items():need(sha(p)==h,'input changed during check '+str(p))
for path,info in provider.items():need(sha(path)==info['sha256'] and str(Path(path).resolve())==info['realpath'],'provider changed during check '+path)
need(sha(out)==r['object_sha256'],'output changed during check')
print(json.dumps({'status':'PASS','graph_rows':91,'author_exit':r['exit'],'provider_files':len(provider),
 'previous_92_algebra_object_matches':True,'independent_91_graph_review':'PASS',
 'object_sha256':r['object_sha256']},indent=2))
