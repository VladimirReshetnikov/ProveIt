from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-local-word-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='08fe37cf70ecbcbd6ec88d565322be49a7be4f10c41dad0fb2df5614a171c4b3','result hash')
need(sha(O/'terminal.json')=='f4e93b1bbe068139c7f60a53e67f2a3308a27e3bc5b25952ce499ee6a1203d88','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-localword-akvztvhn');obj=root/'Trace75BFSLocalWord.olean';source=P/'Trace75BFSLocalWord.lean';code='56a79783146f91246010e77d67618f4abee77fac833f29bbfb701e7eab31c6c5'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='44c32916a71327fcec252f542a534c60c52ed45b6fb102692c270cc52aa00d07','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSLocalWord.field_cast' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75BFSLocalWord.graph_local_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='71466a6f5a3a7e9fcbf7963b2d9430952e7f81cfd65b023f17fc09bfb78ecbda','object')
imports=['Init','Init','Trace75BFSFieldCastBridge','Trace75BFSTileMatch','Trace75BFSAnchor','DiophantineConsistency.CompactLocalWord']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-local-word-prelaunch-independent/check.py'))
