from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-field-cast-bridge-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='a844c52fefb362b2ac6f6d97a328c270610e321b1d70723560a9c7a29dab52a8','result hash')
need(sha(O/'terminal.json')=='f7f791d26e7049aa3a5cfb9894df72d85f03c4c586bd36a240e18e4f41370a4e','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-fieldcast-7s_1mnoi');obj=root/'Trace75BFSFieldCastBridge.olean';source=P/'Trace75BFSFieldCastBridge.lean';code='4138565a914e74ae8448f1f717296f34e0ef973a05ef28dc131b1c6f64b2a58d'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='6ba23fe536f6515500ed4e5c544b865a062874306c1e3165b253f4295bc557c4','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSFieldCastBridge.lookup_row' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSFieldCastBridge.lookup_matches' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='5bdf2b8dce3c1dbbce5f62efc55a9d87df87e273ce4c985dac81d230e356aff2','object')
imports=['Init','Init','Trace75BFSTileMatch','DiophantineConsistency.CompactFieldCastBridge']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-field-cast-prelaunch-independent/check.py'))
