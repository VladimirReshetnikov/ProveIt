from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-tile-match-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='ad342d9ab25c03b26a6e9044c7f10675a482d026a85b043c149cce2bb725cb62','result hash')
need(sha(O/'terminal.json')=='f5d2c1c0a6274f1fc061d1426e1ea59e01e08abc3b5685039fb4ff199b396a30','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-tilematch-spgmvnyq');obj=root/'Trace75BFSTileMatch.olean';source=P/'Trace75BFSTileMatch.lean';code='a1a20e4cf3e29818eff33b5e80bdfc0b903f55cf38af5cd6697a0cb0da9d8526'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='a15daed8a8e399d2507c9a03c3fab5c42c03ccb8397e2e756444a003bef038f5','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSTileMatch.graph_tile_match' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='0043419a5d27dfeea59e0583718c1d105b5d860cfb77f846d9ce7a1ce93355b2','object')
imports=['Init','Init','Trace75BFSAllBlockWord','Trace75BFSFieldMarkers','Trace75BFSUniformDecoder','DirectBFSFieldSlices','DirectBFSTileFields','DiophantineConsistency.BlockCyclicIndex']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-tile-match-prelaunch-independent/check.py'))
