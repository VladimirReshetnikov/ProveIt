from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-all-block-word-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='46d8ffd2a89c1e7a955e54f763668bf0d03b2bb24aeea495b3a9bc6094756932','result hash')
need(sha(O/'terminal.json')=='638abb41f85ec52f6cca75cf37d3988c761b5b024ecb11e85043a5d01ac47611','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-allblockword-_c_e6kmb');obj=root/'Trace75BFSAllBlockWord.olean';source=P/'Trace75BFSAllBlockWord.lean';code='d2157679d53263ce59e7cf094830f6c8ba577135ebdd2e9c650a3d88e63f7c23'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='4172a061d494ceae5a4e0684077ea682203f22f359505a95dd3cb54ce7a59081','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSAllBlockWord.graph_all_block_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='ad6eda0a5c1a390493a943e97d08e84dc0eed993918d16122d0c0b3bebbfa23a','object')
imports=['Init','Init','Trace75BFSAllBlocks','Trace75BFSSpatialSuccessor','DirectBFSOrbitRowWord','DiophantineConsistency.ArithmeticPackingBlocks']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-all-block-word-prelaunch-independent/check.py'))
