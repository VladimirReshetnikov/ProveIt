#!/usr/bin/env python3
"""Audit the transport-restricted 88/89 existence theorem without Lean."""
from hashlib import sha256
import json,os,re,subprocess,sys
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-absorb88-probe';O=H/'observations'
LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib');BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
PINS={BASE:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 O/'graph-attempt01/result.json':'a87d71f4ac9aba2bde66ae73019890db0706c84305991b84ab54f9a9f4ffc905',
 O/'first-attempt01/result.json':'a2acd384312b90b9f5bfe72ed07b5b0a43a9c9bcb072dc26cc24b296e9fbbae5',
 O/'signs-attempt03/result.json':'edcbaf30d57eaee4559bd372057f40a7799de84d9265ee6a449eb1c4bdab7ffa',
 O/'gap-attempt01/result.json':'db5d74fc8f779e5a6443d1885b299307b5c3279d0615909d82de774f45fd77c9',
 O/'reflection-attempt01/result.json':'ae893be9eaa536d060a6b22e34b604c2fe5f3c8ae78e6e5fc82d989eda758c00',
 O/'forward-attempt01/result.json':'560c72897cbdd9056be51bca1b1e2a349c62d0f303134d5d5ddce56456277990',
 O/'inverse-attempt02/result.json':'6eda40d6aa773ec3a57d2854e067ac1b92b9c3ffb627e72e615c8e70e8560df6',
 O/'select-attempt01/result.json':'e8928c54195ccaacbd54a58a56c1b475345475e3b239c29441a2cc0307fecb39',
 O/'conditional-attempt01/result.json':'e2e2dea05988590e9b2d13769ea2b41aae2448b33ba8b15e3f772d0a74a6a05b',
 O/'restricted-attempt01/result.json':'8f1e126fb5fd320c3a2c92b8b03397d5de9b2de920d085d6b730502a9c8d2064',
 O/'signs-attempt01/result.json':'b81ab5e21710dd7ae668e82dc8fa5d02eb9d8da6347de68983fd282452ec306c',
 O/'signs-attempt02/result.json':'3970768cc47f28cbda704847806449b6440d45f196b4141d9fa5bf2719114fb7',
 O/'inverse-attempt01/result.json':'da5daa1f52a1e21bebbaec0a64fa48da6edd02e74dbee31a016f90c3f20a6a57',
 H/'graph-dag.json':'84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25',
 D/'research/ordinary12-absorb89-probe/graph-dag.json':'280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
base=json.loads(BASE.read_text());need(base['exit']==0 and base['union_unchanged'],'base receipt')
def inventory():
 x={p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
 need(len(x)==1291 and x==base['union'],'provider union drift');return x
before=inventory();accepted={};preds={};samples=0
groups=[('graph-attempt01','run-graph.py',['Absorb88Graph']),('first-attempt01','run-first.py',['Absorb88First','Absorb88FirstQuotient']),
 ('signs-attempt03','run-signs.py',['Absorb88Transport','Absorb88Signs']),('gap-attempt01','run-gap.py',['Absorb88Divisibility','Absorb88Gap']),
 ('reflection-attempt01','run-reflection.py',['Absorb88FullReflection','Absorb88ModelReflection']),('forward-attempt01','run-forward.py',['Absorb88Forward']),
 ('inverse-attempt02','run-inverse.py',['Absorb88Inverse']),('select-attempt01','run-select.py',['Absorb88Select']),
 ('conditional-attempt01','run-conditional.py',['Absorb88Conditional']),('restricted-attempt01','run-restricted.py',['Absorb88Restricted'])]
for name,runner,modules in groups:
 obs=O/name;d=json.loads((obs/'result.json').read_text());need(d['status']=='PASS' and sha(H/runner)==d['runner_sha256'],'runner/result '+name)
 need([r['module'] for r in d['stages']]==modules,'stage order '+name);roots=[Path(x) for x in d['lean_path'].split(':')]
 for path,digest in d['predecessors'].items():
  p=Path(path);need(sha(p)==digest,'predecessor drift '+path);preds[path]=digest
  first=next((root/p.name for root in roots if (root/p.name).is_file()),None)
  need(first is not None and sha(first)==digest,'top-level import shadow '+path)
 for i,row in enumerate(d['stages'],1):
  label=f'stage-{i:02}';module=row['module'];root=Path(d['output_root']);source=H/(module+'.lean');snapshot=obs/(label+'.source.lean');copied=root/'src'/(module+'.lean');obj=root/'lib'/(module+'.olean')
  need(row==json.loads((obs/(label+'.json')).read_text()) and row['exit']==0 and row['reason'] is None,'stage receipt '+name)
  need(sha(source)==sha(snapshot)==sha(copied)==row['source_sha256']==d['sources'][module] and sha(obj)==row['object_sha256'],'source/object '+module)
  so=obs/(label+'.stdout');se=obs/(label+'.stderr');need(sha(so)==row['stdout_sha256'] and sha(se)==row['stderr_sha256'] and not se.read_bytes(),'logs '+module)
  text=so.read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostics '+module)
  reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
  need(reports and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axioms '+module)
  pre=row['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight')
  for x in row['samples']:
   need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'resource sample');samples+=1
  for imported in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
   if imported in modules:need(modules.index(imported)<i-1,'forward stage import '+module)
   if '.' not in imported:need(any((r/(imported+'.olean')).is_file() for r in roots),'missing top-level import '+imported)
  accepted[module]=row['object_sha256']
for name in ('signs-attempt01','signs-attempt02','inverse-attempt01'):
 d=json.loads((O/name/'result.json').read_text());need(d['status']=='FAILED','historical failure '+name)
 last=d['stages'][-1];log=(O/name/('stage-%02d.stdout'%len(d['stages']))).read_text()
 if name.startswith('signs-'):need(last['exit']==0 and 'warning:' in log,'warning-rejected '+name)
 else:need(last['exit']!=0 and 'error' in log,'inverse failure')
run=subprocess.run([sys.executable,'-I','-S','-B',str(H/'check-dag.py')],capture_output=True,timeout=30)
need(run.returncode==0 and not run.stderr and json.loads(run.stdout)['rows']==88,'graph comparison')
restricted=(H/'Absorb88Restricted.lean').read_text();conditional=(H/'Absorb88Conditional.lean').read_text();select=(H/'Absorb88Select.lean').read_text();gap=(H/'Absorb88Gap.lean').read_text()
need('theorem positive_zero_iff (p : Fin 4 → ℕ) (hb : 0<(p 0:V))' in restricted,'restricted port assumption')
need('InternalZero (graph (integerPorts p)).output v ∧' in restricted and '(v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5)) ↔' in restricted,'restricted existential bound')
need('Absorb88Conditional.exists_89_of_transport p hb' in restricted and 'Absorb89Transport.transport p v hb hv hz' in restricted,'both directions')
need('theorem exists_88_of_89' in conditional and 'theorem exists_89_of_transport' in conditional,'conditional maps')
need('negative_branch_preserves' in select and 'Absorb88Gap.positive_gap p w' in select and 'threshold p w<w 7' in select,'reflection/threshold selection')
need('Absorb88Divisibility.graph_divisibility' in gap and 'ell+k<v 7' in gap,'positive gap')
need(inventory()==before,'provider changed during audit')
for path,digest in preds.items():need(sha(path)==digest,'predecessor changed '+path)
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','accepted_modules':len(accepted),'restricted_object':accepted['Absorb88Restricted'],
 'predecessor_files':len(preds),'resource_samples':samples,'selected_union_files':len(before),'graph_rows':88,
 'scope':'transport-restricted existence equivalence in IΣ₁ models; selected provider receipt audit, no Lean replay or unrestricted halt/iPRA theorem'},indent=2,sort_keys=True))
