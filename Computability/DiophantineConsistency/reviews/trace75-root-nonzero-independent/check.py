#!/usr/bin/env python3
"""Audit conditional root packets and post-hoc provider resolution; no Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe'
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def audit(attempt,source,runner,obj,report):
 o=P/'observations'/attempt;s=P/source;t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);inputs=t['inputs']
 need(t['exit']==0 and t['reason'] is None,'exit')
 need(sha(P/runner)==t['runner_sha256'] and sha(s)==inputs[str(s)]==sha(o/'source.txt')==sha(root/source),'source/runner')
 for p,h in inputs.items():need(sha(p)==h,'input '+p)
 need(sha(root/(s.stem+'.olean'))==t['object_sha256']==obj,'output')
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
 need((o/'stdout').read_text()==f"'{report}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms/diagnostics')
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)
 modules=['DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','ProductRoot','DiophantineConsistency.ArithmeticGcdNormalization','TenPositiveDoubling','ScaledSquare']
 if attempt.startswith('nonzero'):modules.insert(0,'Trace75Root')
 need(all(m in modules for m in imports),'uncovered direct imports')
 selected=[]
 for m in modules:
  rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
  need(p is not None,'selected '+m)
  need(any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in inputs.items()),'unpinned '+m)
  selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
 return {'object_sha256':obj,'source_sha256':sha(s),'runner_sha256':sha(P/runner),'selected':selected}
a=audit('root-attempt02','Trace75Root.lean','run-v2.py','bf8d56a7526a5324d04c7178d8265e619a15aa624d117d11ba8b864831624958','Trace75Root.roots_of_representatives')
b=audit('nonzero-attempt02','Trace75RootNonzero.lean','run-nonzero-v2.py','35e467ec9e32fb7e0e0b02f917c576811341e89d4a593ccc8dcd8603a5474802','Trace75RootNonzero.roots_of_positive_representatives')
need(next(x for x in b['selected'] if x['module']=='Trace75Root')['sha256']==a['object_sha256'],'root object')
for m in ['DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','ProductRoot']:
 x=next(x for x in a['selected'] if x['module']==m);y=next(x for x in b['selected'] if x['module']==m)
 need(x['path']==y['path'] and x['sha256']==y['sha256'],'selected '+m)
for name in ['root-attempt01','nonzero-attempt01']:
 t=json.loads((P/'observations'/name/'terminal.json').read_text());need(t['exit']!=0 and t['object_sha256'] is None,'failed attempt '+name)
print(json.dumps({'status':'PASS','root':a,'nonzero':b,'lean_replayed':False,'scope':'post-hoc selected file audit, not transitive provenance'},indent=2,sort_keys=True))
