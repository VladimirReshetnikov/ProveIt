#!/usr/bin/env python3
"""Portable checks of file identity, source structure, and source reconstruction.
This checker does not assert machine runtime or logical completeness.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
import source_language as s,build221 as b
ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'reproduced';OUT.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for rel,h in manifest.items():assert sha(ROOT/rel)==h,rel
expected={
 'cantor-fast-f0-s1-p1.sites.json':(206,4465,37,6),
 'omit-zero-push.sites.json':(205,4725,38,6),
 'merged-n-0-0.sites.json':(204,4719,35,6),
 'merged-n-0-1.sites.json':(204,4700,35,6),
 'merged-n-1-0.sites.json':(204,4719,35,6),
 'merged-n-1-1.sites.json':(204,4700,35,6),
 'prefix-q0-i2.sites.json':(206,4782,37,10),
 'grammar204-balanced-best.sites.json':(204,None,None,7),
 'zero_abstract_r6.sites.json':(205,4744,38,6),
}
checks=[]
for name,want in expected.items():
 path=ROOT/'candidates'/name;rows=json.loads(path.read_text());tree=s.tree(rows);metrics=s.metrics(tree)
 for field,v in zip(['dag_nodes','leaf_occurrences','maximum_depth','maximum_zero_run'],want):
  if v is not None:assert metrics[field]==v,(name,field,metrics[field],v)
 assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows),name
 checks.append({'source':name,'sha256':sha(path),'metrics':metrics,'independent_CFG_agreement':True})
for script in ['cantor_fast_orientation.py','merged_n.py']:
 run=subprocess.run([sys.executable,str(ROOT/'code'/script)],text=True,capture_output=True)
 (OUT/(script+'.log')).write_text(run.stdout+run.stderr)
 assert run.returncode==0,(script,run.stderr)
for name in ['cantor-fast-f0-s1-p1.sites.json','cantor-fast-f0-s1-p1.tm']+[f'merged-n-{x}-{y}.sites.json'for x in [0,1]for y in [0,1]]:
 assert (OUT/name).read_bytes()==(ROOT/'candidates'/name).read_bytes(),('reconstruction',name)
base=s.tree(json.loads((ROOT/'inputs/sites218.json').read_text()))
old=s.subtree(base,'11111')
assert len(s.sites(old[0]))==19 and len(s.sites(old[1]))==7
omitted=s.replace(base,'11111',old[1])
assert s.compact(s.sites(omitted))==(ROOT/'candidates/omit-zero-push.sites.json').read_bytes()
for name,n in [('cantor-fast-f0-s1-p1.tm',229),('omit-zero-push.tm',218)]:
 table=b.read_table((ROOT/'candidates'/name).read_bytes());assert len(table)==2*n
report={'status':'PASS','manifest_files':len(manifest),'source_checks':checks,'exact_reconstruction':True,'finite_arithmetic_diagnostics':'Executed by the reconstructed Cantor script; all-natural proof is separate in report.','scope':'File identities, source structure, macro arithmetic diagnostics, reconstruction, and physical census. No new runtime, startup, or completeness theorem.'}
(OUT/'checkpoint_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
