from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-original-word-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='746ed1e8d13ee775b65ecc524e3f345a4bfef59e307afe2e42e16b1fd4868aec','result hash')
need(sha(O/'terminal.json')=='3549393cbe3d97bcca1df55ebfa9aba2bce3cd2dd923f447033c97a09e991bc4','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-originalword-761j1h5p');obj=root/'Trace75BFSOriginalWord.olean';source=P/'Trace75BFSOriginalWord.lean';code='2def28afe35fda8bf52b7e2944b1841fc25367485b6259a684f284909dc3b38b'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='367610c82e3f0865f71878c6d83d470186a15a735beb27f2c8dd96a2c5bf2dfd','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSOriginalWord.graph_original_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='7993899f413a29c339018d2aa71879f7c04968c080b431a5d1407b49d5670066','object')
imports=['Init','Init','Trace75BFSModelWordTransfer','Trace75BFSLocalWord']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-original-word-prelaunch-independent/check.py'))
