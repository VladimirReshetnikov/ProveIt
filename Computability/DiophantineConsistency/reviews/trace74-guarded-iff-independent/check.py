#!/usr/bin/env python3
"""Audit guarded-model receipts and selected overlay modules; no Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-mask-coordinate-ring-probe'
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def audit(attempt,source,runner,obj,report,expected_imports):
 o=P/'observations'/attempt;s=P/source;t=json.loads((o/'terminal.json').read_text());r=pathlib.Path(t['output_root']);inputs=t['inputs']
 need(t['exit']==0 and t['reason'] is None,'exit')
 need(sha(P/runner)==t['runner_sha256'] and sha(s)==inputs[str(s)]==sha(o/'source.txt')==sha(r/source),'runner/source')
 need(sha(r/(s.stem+'.olean'))==t['object_sha256']==obj,'object')
 for p,h in inputs.items():need(sha(p)==h,'pinned input '+p)
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'log hashes')
 need((o/'stdout').read_text()==f"'{report}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms/diagnostics')
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==expected_imports,'imports')
 roots=t['lean_path'].split(':'); selected=[]
 modules=['Trace74Mask','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticGcdNormalization']
 if attempt.startswith('iff-'):modules.insert(0,'Trace74Guarded')
 for m in modules:
  rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in roots if (pathlib.Path(z)/rel).is_file()),None)
  need(p is not None,'missing selected '+m)
  matches=[(q,h) for q,h in inputs.items() if pathlib.Path(q).resolve()==p.resolve() and h==sha(p)]
  need(matches,'selected object not pinned '+m)
  selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p)})
 return {'object_sha256':obj,'runner_sha256':sha(P/runner),'source_sha256':sha(s),'selected':selected}
a=audit('guarded-attempt04','Trace74Guarded.lean','run-guarded-v4.py','9729356ff22b501454abbd77b7319bb00b222f83a6a4b79404ebef93281dceda','Trace74Guarded.guarded_to_old',['Trace74Mask','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticGcdNormalization'])
b=audit('iff-attempt02','Trace74GuardedIff.lean','run-iff-v2.py','841fa8255b84d3b6e9de8cf0ce25c995c6c94e8fd5ee6694b48803e994fec255','Trace74GuardedIff.guarded_positive_zero_iff',['Trace74Guarded'])
need(next(x for x in b['selected'] if x['module']=='Trace74Guarded')['sha256']==a['object_sha256'],'iff provider')
for m in ['Trace74Mask','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticGcdNormalization']:
 x=next(x for x in a['selected'] if x['module']==m);y=next(x for x in b['selected'] if x['module']==m)
 need(x['path']==y['path'] and x['sha256']==y['sha256'],'overlay selection '+m)
print(json.dumps({'status':'PASS','guarded':a,'iff':b,'lean_replayed':False,'scope':'post-hoc selected files; no transitive provenance audit'},indent=2,sort_keys=True))
