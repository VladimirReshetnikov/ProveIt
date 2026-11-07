#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-recipe-scoped-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-compact-recipe-scoped-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='ceb8ca4c78814dfc16cf8335ee4d5c0a71ba0308e21b7cf033dbcaa360e7af19' and sha(A/'outer-terminal-author-record.json')=='f0da77ec65816d2d6b2bdc12f6d9062648a4b1a972cb1e531de7bdee53ea16ec';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(8270,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==sha(P/'run.py')=='4cb59c1e972474df745562b764d01afb4ac711b82fdfc57e8fcade0c07bfb225';names=['Sign33MacroRecipe','Sign33MacroScoped'];objects=['ad746dde4c868da21963986e3255688d531ef7bed07d16a16970ac4819433045','432dc5d7ad33633d6ac70dee255ed4da869c692e9b3b9ce23e017ed428f39e00'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroLanguage','9e1b3c12f306411cfc650eaf0182042ae607a81b4b75f8cc660f0daf46bea4d3') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i==0:assert log==''
 else:assert "'DiophantineConsistency.Sign33MacroScoped.recipe_well_scoped' does not depend on any axioms" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-compact-recipe-scoped-prelaunch-frontier-independent/check.py';assert sha(review)=='fdb41ea35c6be552c7d4259b9dac4ba5b8c0845bbf22e8a3e66573378f4d9122';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':8270,'stages':2,'guard_slots':200,'overlay_links':1057,'scope':'Lean recipe data and axiom-free Boolean binder scopedness only; no semantic equality or JSON/prose binding'},indent=2,sort_keys=True))
