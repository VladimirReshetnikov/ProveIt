#!/usr/bin/env python3
"""Authored release verifier. No network and no upstream program execution.
Hash-check originals, replay an explicit allowlist in isolated temporary copies.
"""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def validate(root):
 manifest=json.loads((root/'MANIFEST.json').read_text());rows=manifest['files']
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
 expected=set(rows)|{'MANIFEST.json'}
 if actual!=expected:raise RuntimeError('inventory difference: '+str(sorted(actual^expected)))
 for name,row in rows.items():
  p=root/name
  if p.is_symlink() or sha(p)!=row['sha256'] or p.stat().st_size!=row['bytes']:raise RuntimeError('manifest mismatch: '+name)
 return manifest

def run(root,cmd,optimized):
 full=[sys.executable]+(['-O'] if optimized else [])+cmd
 p=subprocess.run(full,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=240)
 if p.returncode:raise RuntimeError('Command failed: '+' '.join(full)+'\n'+p.stdout[-6000:])
 return {'command':cmd,'optimized':optimized,'status':'PASS'}

def replay(original,manifest,optimized):
 contract=json.loads((original/'REPLAY.json').read_text());results=[]
 with tempfile.TemporaryDirectory(prefix='con-zfc-r11-') as td:
  work=Path(td)/'packet';shutil.copytree(original,work,ignore=shutil.ignore_patterns('__pycache__'))
  baseline={n:sha(work/n) for n in contract['rebuild_exact']}
  before={str(p.relative_to(work)) for p in work.rglob('*') if p.is_file()}
  for cmd in contract['commands']:results.append(run(work,cmd,optimized))
  for n,h in baseline.items():
   if sha(work/n)!=h:raise RuntimeError('non-identical rebuilt artifact: '+n)
  after={str(p.relative_to(work)) for p in work.rglob('*') if p.is_file()}
  extra=after-before-set(contract['generated_files'])
  if extra:raise RuntimeError('unlisted generated files: '+str(sorted(extra)))
  # Only the precisely listed reproducible outputs or receipts may change.
  allowed=set(contract['rebuild_exact'])|set(contract['generated_files'])
  for n,row in manifest['files'].items():
   if n not in allowed and sha(work/n)!=row['sha256']:raise RuntimeError('unexpected replay mutation: '+n)
 return {'status':'PASS','optimized':optimized,'commands':results,'byte_identical_rebuilt_files':len(baseline)}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--quick',action='store_true',help='Normal Python only; full default also runs optimized Python.');ap.add_argument('--manifest-only',action='store_true');ap.add_argument('--output',type=Path,help='Optional receipt path outside the release tree.');args=ap.parse_args()
 t=time.time();m=validate(ROOT);out={'status':'PASS','files_sha256_verified':len(m['files']),'manifest':'MANIFEST.json','no_upstream_code_executed':True,'scope':'Finite exact algebra, data, transcription, source restoration and negative controls. Mathematical reduction proofs remain essential; no kernel certificate.'}
 if not args.manifest_only:out['replays']=[replay(ROOT,m,False)]+([] if args.quick else [replay(ROOT,m,True)])
 out['elapsed_seconds']=round(time.time()-t,3)
 if args.output:
  p=args.output.resolve()
  if ROOT==p or ROOT in p.parents:raise ValueError('Receipt output must be outside the immutable release tree')
  p.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
