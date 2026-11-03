#!/usr/bin/env python3
"""Audit the signed-ring 86 graph experiment without invoking Lean."""
from hashlib import sha256
import json,os,re,subprocess,sys
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-absorb86-probe';A=H/'observations/graph-attempt01';BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json';LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib')
PINS={H/'graph-dag.json':'fe4fad3297719f8cf60ec15fe608ebf089e3fed413a2ded7f078b2d42db3f1f8',
 H/'Absorb86Graph.lean':'257b5609270b96fbf718a3be5b7671f149dcbf3a4122503338deb229f31bdb82',
 H/'check-dag.py':'a2725e579d123eef33fcb48b01b8253957e729961cb68f45420f159ac97f9aac',
 H/'observations/dag-attempt01/result.json':'83db65697953458d587f1fc5d753ae1eeee536eef7787766e6ad69f4e725df26',
 A/'result.json':'66cd717cdbc1ee343d0aa69e69a5ea80076070e68efeb3184a3940bfa0f739a4',
 D/'research/ordinary12-absorb89-probe/graph-dag.json':'280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd',
 BASE:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'pin drift '+str(p))
a=json.loads((H/'graph-dag.json').read_text());b=json.loads((D/'research/ordinary12-absorb89-probe/graph-dag.json').read_text())
expected=[]
for n,op,x,y in b['source']:
 if n in ('g31','folded_kBt','folded_g31'):continue
 if n=='g33':need((op,x,y)==('*','qm','folded_g31'),'old root');y='r'
 expected.append([n,op,x,y])
need(a['source']==expected and len(expected)==86,'DAG transformation')
src=(H/'Absorb86Graph.lean').read_text();body=src.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\nvariable {R : Type*}',1)[0];lines=body.strip().splitlines()
signature=[f'let {n} : Expr (Fin 12) := .var {i}' for i,n in enumerate(a['witnesses'])]+[f'let {n} : Expr (Fin 12) := .constant (p {i})' for i,n in enumerate(a['fixed_numerals'])]
need([x.strip() for x in lines[:16]]==signature,'slot bindings')
rows=[]
for line in lines[16:-1]:
 z=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);need(z is not None,'unparsed row '+line)
 n,x,op,y=z.groups();rows.append([n,op,int(x) if x.isdigit() else x,int(y) if y.isdigit() else y])
need(rows==a['source'] and lines[-1].strip()=='⟨A0, A1, N, P12⟩','Lean graph rows/fields')
parents={n:(x,y) for n,_,x,y in rows};live=set();todo=['P12']
while todo:
 n=todo.pop()
 if n in parents and n not in live:live.add(n);todo.extend(parents[n])
need(len(live)==86,'dead graph rows')
out=subprocess.run([sys.executable,'-I','-S','-B',str(H/'check-dag.py')],capture_output=True,timeout=30)
need(out.returncode==0 and not out.stderr and json.loads(out.stdout)==json.loads((H/'observations/dag-attempt01/result.json').read_text()),'external DAG replay')
ob=subprocess.run([sys.executable,'-I','-S','-B',str(H/'check-obstruction.py')],capture_output=True,timeout=30)
need(ob.returncode==0 and not ob.stderr,'obstruction checker')
example=json.loads(ob.stdout);need(example['A0']==0 and example['Bt']>0 and example['r_new']<0 and (example['A1']!=0 or example['N']!=0),'first-factor-only counterexample')
d=json.loads((A/'result.json').read_text());need(d['status']=='PASS' and len(d['stages'])==1 and sha(H/'run-graph.py')==d['runner_sha256'],'runner result')
r=d['stages'][0];need(r==json.loads((A/'stage-01.json').read_text()) and r['exit']==0 and r['reason'] is None,'stage receipt')
need(sha(A/'stage-01.source.lean')==sha(H/'Absorb86Graph.lean')==r['source_sha256'],'stage source')
obj=Path(d['output_root'])/'lib/Absorb86Graph.olean';need(sha(obj)==r['object_sha256']=='19ea430fa07208907e908de42fcba8d1d419f728b06eb0202a7f87744c2f4e96','stage object')
need(sha(A/'stage-01.stdout')==r['stdout_sha256'] and sha(A/'stage-01.stderr')==r['stderr_sha256'] and not (A/'stage-01.stderr').read_bytes(),'stage logs')
logs=(A/'stage-01.stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',logs) and 'sorryAx' not in logs,'diagnostics')
for n in ('first_eval','main_eval','ordinary_eval'):
 need(f"'FreeJAbsorb86.{n}' depends on axioms: [propext]" in logs,'axiom '+n)
pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight')
for x in r['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'resource sample')
paths=[Path(x) for x in d['lean_path'].split(':')]
for p,digest in d['predecessors'].items():
 p=Path(p);need(sha(p)==digest,'producer drift');first=next((x/p.name for x in paths if (x/p.name).is_file()),None)
 need(first is not None and sha(first)==digest,'producer selection '+str(p))
base=json.loads(BASE.read_text())
def union():return {p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
need(base['exit']==0 and base['union_unchanged'] and union()==base['union'] and len(base['union'])==1291,'selected base union')
need('Function.update v 7 (ell+k+v 7-k*Bt)' in src and all('theorem '+n in src for n in ('first_eval','main_eval','ordinary_eval')),'signed map statements')
for p,h in PINS.items():need(sha(p)==h,'changed input '+str(p))
need(union()==base['union'],'selected base union changed')
print(json.dumps({'status':'PASS','rows':len(rows),'live':len(live),'output_sha256':r['object_sha256'],
 'obstruction_first_factor_zero':True,'obstruction_full_zero':False,'sample_negative_new_witness':example['r_new'],
 'scope':'signed-ring residual mapping and external DAG/receipt audit only; no positivity, reverse, halt or iPRA theorem'},indent=2,sort_keys=True))
