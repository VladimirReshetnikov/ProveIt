#!/usr/bin/env python3
"""Fresh Lean4.32 build of the exact decoder-source binding, no Mathlib needed."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, tempfile, time
ROOT=Path(__file__).resolve().parent
ORDER=['BusyBeaver.ZFC.RegisterPath','BusyBeaver.ZFC.RMDag','BusyBeaver.ZFC.RMEquiv',
 'BusyBeaver.ZFC.RMBisim','BusyBeaver.ZFC.Dag222','BusyBeaver.ZFC.Dag219',
 'BusyBeaver.ZFC.DagDom','BusyBeaver.ZFC.DagPerm','BusyBeaver.ZFC.KSource215Data',
 'BusyBeaver.ZFC.SiteCoverage','FramedWindow','DecoderCertificate','K215Decoder',
 'DecoderPaths','DecoderSourceBinding']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--lean',default='lean');ap.add_argument('--out',type=Path)
 ap.add_argument('--threads',type=int,default=1);ap.add_argument('--memory-mib',type=int,default=4096)
 args=ap.parse_args();lean=shutil.which(args.lean) or str(Path(args.lean).resolve())
 version=subprocess.check_output([lean,'--version'],text=True).strip()
 if 'version 4.32.0' not in version:raise RuntimeError('Use the pinned official Lean4.32.0 release: '+version)
 out=(args.out or Path(tempfile.mkdtemp(prefix='k215-source-paths-'))).resolve()
 out.mkdir(parents=True,exist_ok=True)
 if any(out.iterdir()):raise RuntimeError('Output directory must be empty to ensure a fresh build')
 logs=out/'logs';logs.mkdir()
 index=json.loads((ROOT/'source_index.json').read_text());records=[]
 for x in index['files']:
  src=ROOT/x['path']
  if sha(src)!=x['sha256']:raise RuntimeError('Source identity differs: '+x['path'])
  target=out/x['path'].removeprefix('reference/');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
 env=dict(os.environ,LEAN_PATH=str(out));started=time.monotonic()
 flags=['-j'+str(args.threads),'-M'+str(args.memory_mib)]
 receipt={'status':'RUNNING','version':version,'repository_pin':index['pin'],
  'compiler_flags':flags,'modules':records,
  'new_endpoints':['K215SourcePaths.reaches_primitive','DecoderSourceBinding.source_tree_eq',
   'DecoderSourceBinding.upstream_leaf_reaches','DecoderSourceBinding.upstream_walk_reaches'],
  'scope':'Decoder traversal through the exact upstream source, ending at primitive entry; primitive execution and return are not proved here.'}
 def save():
  receipt['total_seconds']=time.monotonic()-started
  (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 save()
 for module in ORDER:
  rel=Path(module.replace('.','/')).with_suffix('.lean');src=out/rel;obj=src.with_suffix('.olean')
  t=time.monotonic();p=subprocess.run([lean,*flags,'-o',str(obj),str(src)],cwd=out,env=env,text=True,capture_output=True)
  log=logs/(module+'.log');log.write_text(p.stdout+p.stderr)
  rec={'module':module,'exit_code':p.returncode,'seconds':time.monotonic()-t,
   'source_sha256':sha(src),'log_sha256':sha(log)}
  if obj.exists():rec['object_sha256']=sha(obj)
  records.append(rec);print(json.dumps(rec),flush=True);save()
  if p.returncode:
   receipt['status']='FAILED';receipt['failed_module']=module;save()
   raise RuntimeError('Compiler failed; see '+str(log))
  if 'sorryAx' in p.stdout+p.stderr:
   receipt['status']='UNEXPECTED_SORRY';receipt['failed_module']=module;save()
   raise RuntimeError('Unexpected sorryAx in '+module)
 receipt['status']='PASS_FRESH_15_MODULE_BUILD';save();print(str(out/'receipt.json'))
if __name__=='__main__':main()
