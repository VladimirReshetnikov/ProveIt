from pathlib import Path
import hashlib,json,runpy
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency');P=H/'research/trace75-bfs-model-halt-prototype';A=P/'observations/attempt01';O=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(A/'result.json')=='f07f6309693b7259e15bd149a14c2da5e96e50c62b5fc82c43ca60d4fa416a4a','result hash')
need(sha(O/'terminal.json')=='131436b3c3edc596212719a52fb88c0ad62dfa5016fc98ce089610323fc376d3','outer hash')
x=json.loads((A/'result.json').read_text());t=json.loads((O/'terminal.json').read_text());root=Path('/tmp/trace75-bfs-modelhalt-ipf6iwvw');obj=root/'Trace75BFSModelHalt.olean';source=P/'Trace75BFSModelHalt.lean';code='bd7cde350d06e7c0f5e56c6df69bfdfe9d3622aaaaf45ce3b8a95d3a597f3069'
need(x['status']=='PASS' and x['output_root']==str(root) and x['runner_sha256']=='56db6dbc8ab4eebb99e684eb197ef2b725bcfbcb3f2584881e59130aa378100c','child')
need(t['exit']==0 and t['child_result_sha256']==sha(A/'result.json') and t['inputs_before']==t['inputs_after'] and t['wrapper_sha256_before']==t['wrapper_sha256_after']==sha(P/'run-outer.py'),'outer')
for path,h in t['inputs_before'].items():need(sha(path)==h,'outer pin '+path)
for name in ('stdout','stderr'):need(sha(O/name)==t[name+'_sha256'],'outer log')
for name in ('stage','header'):
 rec=x[name];need(rec['status']=='PASS' and rec['exit']==0 and rec['reason'] is None,'status '+name)
 for log in ('stdout','stderr'):
  path=A/(('header.' if name=='header' else '')+log);need(sha(path)==rec[log+'_sha256'],'log hash '+str(path))
 need(not (A/(('header.' if name=='header' else '')+'stderr')).read_bytes(),'stderr '+name)
 for s in [rec['preflight'],rec['postflight'],*rec['samples']]:need(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2,'resources '+name)
need((A/'stdout').read_text()=="'Trace75BFSModelHalt.graph_halts' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axioms')
need(sha(source)==sha(A/'source.txt')==sha(root/source.name)==code,'source copies')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='f3334e5e331cf93540fc45b92d221c4879bc2c0847068b38d96eae83561f56ae','object')
imports=['Init','Init','Trace75BFSOriginalWord','DiophantineConsistency.OldWordIdentification','DiophantineConsistency.ArithmeticWangSoundness']
need(x['header_imports']==imports,'header imports')
need((A/'header.stdout').read_text()=='BEGIN '+str(obj)+'\n'+''.join('IMPORT '+n+'\n' for n in imports)+'END\n','header text')
need(x['stage']['env']==x['env'] and x['env']['LEAN_PATH'].split(':')[0]==str(root) and x['header']['env']=={'PATH':'/usr/bin:/bin'},'env')
print('PASS: outer/child/stage/header, captured inputs/logs/source/object, imports, resource samples')
runpy.run_path(str(H/'reviews/trace75-bfs-model-halt-prelaunch-independent/check.py'))
