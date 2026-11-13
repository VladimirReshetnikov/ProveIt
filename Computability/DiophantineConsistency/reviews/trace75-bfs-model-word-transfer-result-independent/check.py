from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-model-word-transfer-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='b87fe4e0896496d9e38a45325fbb3df732f0afda93793e47125e6a259cedf81a','result hash')
need(sha(O/'terminal.json')=='5935aa3cdc7ff7d31f237a612d8b93651f351de2bd4cfe171c225925bef147bc','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-wordtransfer-dageoevm');obj=root/'Trace75BFSModelWordTransfer.olean';source=P/'Trace75BFSModelWordTransfer.lean';code='debd0f91d603fcd44d6559ce2c7c47cfe4214c93bc15be28cc2617d5894a26ec'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='c6201c905d2eab5b702575c88ed93daf5d16cb0d65bc5dbda7f5da0c1c1ce2b6','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSModelWordTransfer.back_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSModelWordTransfer.direct_cast' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSModelWordTransfer.original_back_cast' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSModelWordTransfer.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='083ef679ae47d02e61a292d127e1f76b1a2b6670e190b0371a8381e123c0992a','object')
imports=['Init','Init','DirectBFSModelIndexMap','Trace75BFSLocalWord','DirectBFSEdgeReflection','DiophantineConsistency.CleanGeometry']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-model-word-transfer-prelaunch-independent/check.py'))
