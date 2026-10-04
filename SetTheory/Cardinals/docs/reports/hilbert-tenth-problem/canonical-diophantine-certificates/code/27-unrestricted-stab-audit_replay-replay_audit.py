#!/usr/bin/env python3
"""Portable replay of byte-frozen independent unrestricted-stabilization audits.
Place in BUNDLE/audit_replay and run with Python -I. --output must be a fresh
external directory. No submitted builder, author checker, upstream schedule,
or Lean is executed. Exact frozen checker bytes are copied outside BUNDLE.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

DAG={'target':'science/evidence/polynomial-dag.json',
     'historical':'/workspace/shared/sandpile-unrestricted-stabilization-20261004/evidence/polynomial-dag.json',
     'sha256':'8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759'}
ROLES={
 'exact':{'checker':'independent_audit/check_exact.py','checker_sha256':'9645445d53332bf7eaaa510d5594d8d198abcbada5a4f064b26db7650bf350a7','receipt':'independent_audit/exact-receipt.json','receipt_sha256':'495fe0a676ab6b124d1103c1b576ccf9d94b4b846cba407f41f5f91ae9f1f2c0','result':'exact-receipt.json'},
 'semantic':{'checker':'independent_audit/check_semantics_fresh.py','checker_sha256':'673cd9ab43cce11f52cc48c628de8d1ff83200d59d4cbd710e453cd03658126e','receipt':'independent_audit/fresh-semantics-receipt.json','receipt_sha256':'46609ce6f2c9819bc928e4df58a53c2277308b3745e4e6bd963845852cd142b8','result':'fresh-semantics-receipt.json'},
 'mutation':{'checker':'independent_audit/challenge_checker.py','checker_sha256':'0e1bfc3cc2aac6441000dea869fa16c570bee5f1aae41928b2a62de22163a696','receipt':'independent_audit/mutation-receipt.json','receipt_sha256':'959ae323c1fbaa6e71531c512aa0f4f7901ff80be65d429997a984a5f3248527','result':'mutation-receipt.json'}}

def require(c,msg):
 if not c:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def beneath(path,root):return path==root or root in path.parents
def snapshot(root):
 result={}
 for p in [root]+sorted(root.rglob('*')):
  st=p.lstat();rel='.' if p==root else p.relative_to(root).as_posix()
  require(not stat.S_ISLNK(st.st_mode),'Symlink not permitted in frozen bundle: '+rel)
  require(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),'Nonregular frozen bundle entry: '+rel)
  record={'kind':'directory' if stat.S_ISDIR(st.st_mode) else 'file','mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns}
  if stat.S_ISREG(st.st_mode):record.update(size=st.st_size,sha256=sha(p.read_bytes()))
  result[rel]=record
 return result
def preserved(a,b):
 changes=sorted(k for k in set(a)|set(b) if a.get(k)!=b.get(k))
 require(not changes,'Frozen bundle changed: '+', '.join(changes[:20]))
def pins(root):
 required={DAG['target']:DAG['sha256']}
 for s in ROLES.values():required.update({s['checker']:s['checker_sha256'],s['receipt']:s['receipt_sha256']})
 for rel,h in required.items():
  p=root/rel;require(p.is_file() and not p.is_symlink(),'Missing frozen input: '+rel)
  require(sha(p.read_bytes())==h,'Frozen pin mismatch: '+rel)
 return required
def external(root,path):
 raw=path.absolute()
 for p in [raw]+list(raw.parents):require(not p.is_symlink(),'Symlink in output path is not permitted')
 p=path.resolve();require(not beneath(p,root),'Replay output must be outside bundle');require(not beneath(root,p),'Replay output cannot contain bundle');return p

def worker(root,work,role):
 require(sys.flags.isolated==1,'Worker must use isolated Python');pins(root);work=external(root,work);spec=ROLES[role]
 copied=work/Path(spec['checker']).name;code=copied.read_bytes();require(sha(code)==spec['checker_sha256'],'Copied checker pin mismatch')
 require(code==(root/spec['checker']).read_bytes(),'Copied checker differs from frozen input')
 receipt=work/spec['result'];require(not receipt.exists(),'Worker receipt already exists')
 originals={k:getattr(Path,k) for k in ['read_bytes','read_text','write_bytes','write_text']};original_run=subprocess.run;original_argv=sys.argv[:]
 redirects=0;dagreads=0;writes=[];children=[]
 def read_target(path):
  nonlocal redirects,dagreads
  if str(path)==DAG['historical']:
   require(role=='mutation','Unexpected historical input read');redirects+=1;dagreads+=1;return root/DAG['target']
  resolved=path.resolve()
  if resolved==(root/DAG['target']).resolve():
   require(role=='exact','Unexpected direct DAG read');dagreads+=1;return path
  require(beneath(resolved,work),'Unapproved worker read');return path
 def write_target(path):
  resolved=path.resolve();require(beneath(resolved,work),'Unapproved worker write');writes.append(resolved.relative_to(work).as_posix());return path
 def read_bytes(path):return originals['read_bytes'](read_target(path))
 def read_text(path,*a,**kw):return originals['read_text'](read_target(path),*a,**kw)
 def write_bytes(path,data):return originals['write_bytes'](write_target(path),data)
 def write_text(path,data,*a,**kw):return originals['write_text'](write_target(path),data,*a,**kw)
 def child_run(command,*a,**kw):
  require(role=='mutation','Unexpected checker subprocess');require(isinstance(command,list),'Unexpected subprocess form')
  child=work/'check_exact.py';normal=[sys.executable,str(child)];optimized=[sys.executable,'-O',str(child)]
  if command[:2]==normal:prefix=2;optimized_flag=False
  elif command[:3]==optimized:prefix=3;optimized_flag=True
  else:raise RuntimeError('Unexpected mutation child executable')
  require(len(command)==prefix+5 and command[prefix]=='--dag' and command[prefix+2]=='--allow-unsealed-test-data' and command[prefix+3]=='--receipt','Unexpected mutation child arguments')
  for i in [prefix+1,prefix+4]:require(beneath(Path(command[i]).resolve(),work),'Mutation child path outside external work')
  require(sha(originals['read_bytes'](child))==ROLES['exact']['checker_sha256'],'Mutation checker pin mismatch')
  # Add isolation only; preserve the frozen test's requested normal/optimized mode.
  isolated=[command[0],'-I']+command[1:];children.append({'optimized':optimized_flag,'isolated':True})
  return original_run(isolated,*a,**kw)
 replacements={'read_bytes':read_bytes,'read_text':read_text,'write_bytes':write_bytes,'write_text':write_text}
 try:
  for k,fn in replacements.items():setattr(Path,k,fn)
  subprocess.run=child_run
  sys.argv=[str(copied)]
  if role=='exact':sys.argv+=['--dag',str(root/DAG['target']),'--receipt',str(receipt)]
  ns={'__name__':'__main__','__file__':str(copied),'__package__':None,'__cached__':None}
  exec(compile(code,str(copied),'exec'),ns)
 finally:
  sys.argv=original_argv;subprocess.run=original_run
  for k,fn in originals.items():setattr(Path,k,fn)
 require(redirects==(1 if role=='mutation' else 0),'Unexpected historical redirect count')
 require(dagreads==(0 if role=='semantic' else 1),'Unexpected DAG read count')
 require(spec['result'] in writes,'Missing receipt write')
 require(len(children)==(20 if role=='mutation' else 0),'Wrong mutation child count')
 require(sha(copied.read_bytes())==spec['checker_sha256'],'Copied checker changed')
 if role=='mutation':require(sha((work/'check_exact.py').read_bytes())==ROLES['exact']['checker_sha256'],'Copied child checker changed')
 trace={'role':role,'checker':spec['checker'],'checker_sha256':sha(code),'source_text_rewritten':False,'frozen_checker_bytes_unchanged':True,'historical_path_fallback':False,'historical_dag_redirects':redirects,'pinned_dag_reads':dagreads,'dag_target':DAG['target'] if dagreads else None,'receipt':spec['result'],'isolated_python':True,'isolated_mutation_children':children}
 (work/'worker-trace.json').write_text(json.dumps(trace,sort_keys=True,indent=2)+'\n')

def replay(root,output):
 output=external(root,output);require(not os.path.lexists(output),'Replay output must be a fresh directory')
 before=snapshot(root);verified=pins(root);output.mkdir(parents=True,exist_ok=False);roles={};failure=None
 try:
  for role,spec in ROLES.items():
   work=output/role;work.mkdir();(work/'tmp').mkdir()
   (work/Path(spec['checker']).name).write_bytes((root/spec['checker']).read_bytes())
   if role=='mutation':(work/'check_exact.py').write_bytes((root/ROLES['exact']['checker']).read_bytes())
   env=os.environ.copy();env.update(TMPDIR=str(work/'tmp'),PYTHONDONTWRITEBYTECODE='1')
   child=subprocess.run([sys.executable,'-I',str(Path(__file__).resolve()),'--bundle-root',str(root),'--worker',role,'--output',str(work)],capture_output=True,text=True,timeout=180,env=env,cwd=str(work))
   (work/'stdout.log').write_text(child.stdout);(work/'stderr.log').write_text(child.stderr)
   require(child.returncode==0,role+' replay failed; see external '+role+'/stderr.log')
   actual=(work/spec['result']).read_bytes();expected=(root/spec['receipt']).read_bytes();require(actual==expected,'Exact receipt mismatch: '+role)
   roles[role]={'checker':spec['checker'],'checker_sha256':spec['checker_sha256'],'expected_receipt':spec['receipt'],'actual_receipt':role+'/'+spec['result'],'receipt_sha256':sha(actual),'receipt_byte_equal':True,'trace':json.loads((work/'worker-trace.json').read_text())}
 except BaseException as exc:failure=exc
 after=snapshot(root);preserved(before,after)
 (output/'bundle-snapshot-before.json').write_text(json.dumps(before,sort_keys=True,indent=2)+'\n');(output/'bundle-snapshot-after.json').write_text(json.dumps(after,sort_keys=True,indent=2)+'\n')
 if failure is not None:raise failure
 result={'verdict':'PASS','schema':'portable-unrestricted-sandpile-independent-audit-replay-v1','adapter_sha256':sha(Path(__file__).read_bytes()),'bundle_paths_are_root_relative':True,'output_paths_are_replay_relative':True,'source_rewriting':False,'historical_path_fallback':False,'all_frozen_inputs_preserved':True,'preservation_checks':['file bytes','file size','file and directory mode','file and directory mtime_ns','entry inventory'],'bundle_entries_checked':len(before),'pinned_inputs':verified,'roles':roles,'scope':'Only the frozen independent exact, semantic and mutation auditors are executed. No submitted builder, author checker, upstream program, schedule, or Lean is executed.'}
 (output/'replay-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2))

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);parser.add_argument('--bundle-root',type=Path,default=Path(__file__).resolve().parent.parent,help=argparse.SUPPRESS);parser.add_argument('--worker',choices=sorted(ROLES),help=argparse.SUPPRESS);args=parser.parse_args()
 require(sys.flags.isolated==1,'Invoke replay with python -I');require(not args.bundle_root.is_symlink(),'Symlink bundle root is not permitted');root=args.bundle_root.resolve();require(root.is_dir(),'Bundle root does not exist')
 if args.worker:worker(root,args.output,args.worker)
 else:replay(root,args.output)
if __name__=='__main__':main()
