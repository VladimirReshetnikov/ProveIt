#!/usr/bin/env python3
"""Clean portable replay of the authored direct builders, normal and optimized.
Authenticates release files; does not execute any inert upstream source.
Independent semantic/algebra audits live in the enclosing audit packet.
"""
import argparse,hashlib,json,pathlib,shutil,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent

def must(p,m):
 if not p:raise ValueError(m)
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=ROOT/'CLEAN_REBUILD.json');args=p.parse_args()
 expected=json.loads((ROOT/'RELEASE_SHA256.json').read_text());whitelist=json.loads((ROOT/'RELEASE_WHITELIST.json').read_text())['files']
 for name,digest in expected.items():must(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'release hash mismatch: '+name)
 reports=[]
 with tempfile.TemporaryDirectory(prefix='direct-round13-replay-') as t:
  stage=pathlib.Path(t)/'portable';stage.mkdir()
  for name in whitelist:
   src=ROOT/name;dst=stage/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  for optimized in [False,True]:
   run=pathlib.Path(t)/('optimized' if optimized else 'normal');run.mkdir()
   py=[sys.executable]+(['-O'] if optimized else [])
   jobs=[('projected',['build_projected.py','--output',str(run/'projected')]),('projected_signed_template',['build_projected.py','--integer-template','--output',str(run/'projected_signed_template')]),('projected_guarded_integer',['build_integer.py','--source',str(run/'projected_signed_template'),'--output',str(run/'projected_guarded_integer'),'--free-quotients']),('projected_integer',['build_sign_normalized.py','--source',str(run/'projected_signed_template'),'--prior-integer',str(run/'projected_guarded_integer'),'--output',str(run/'projected_integer')]),('forward',['build_forward.py','--output',str(run/'forward')])]
   compared=0
   for name,cmd in jobs:
    proc=subprocess.run(py+cmd,cwd=stage,text=True,capture_output=True);must(proc.returncode==0,'build failed '+name+': '+proc.stderr)
    for original in sorted((stage/name).glob('*.json')):
     regenerated=run/name/original.name;must(regenerated.exists(),'missing output '+str(regenerated));must(original.read_bytes()==regenerated.read_bytes(),'rebuild mismatch '+name+'/'+original.name);compared+=1
   reports.append({'optimized':optimized,'variants':5,'exact_json_files_compared':compared,'status':'PASS'})
 receipt={'status':'PASS','portable_whitelist_files':len(whitelist),'authenticated_payloads':len(expected),'runs':reports,'scope':'byte-exact clean rebuild of authored Python only; no theorem proving and no upstream code execution'}
 args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
