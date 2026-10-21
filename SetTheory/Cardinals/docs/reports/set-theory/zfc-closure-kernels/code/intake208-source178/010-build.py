#!/usr/bin/env python3
"""Fresh serial Lean kernel replay. No cached project objects are imported."""
import argparse, hashlib, json, os, shutil, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FILES=['FramedWindow.lean','DecoderCertificate.lean','K215Decoder.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--lean',required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 lean=str(Path(a.lean).resolve());out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
 for n in FILES:shutil.copyfile(ROOT/n,out/n)
 shutil.copyfile(ROOT/'generate_data.py',out/'generate_data.py');shutil.copytree(ROOT/'inputs',out/'inputs')
 q=subprocess.run(['python3','-B','generate_data.py'],cwd=out,text=True,capture_output=True)
 (out/'generation.log').write_text(q.stdout+q.stderr);assert q.returncode==0
 assert (out/'K215Decoder.lean').read_bytes()==(ROOT/'K215Decoder.lean').read_bytes(),'generated literal data mismatch'
 logs=out/'logs';logs.mkdir();env=dict(os.environ);env['LEAN_PATH']=str(out)
 version=subprocess.check_output([lean,'--version'],text=True).strip();records=[]
 for n in FILES:
  cmd=[lean,'-o',str(out/Path(n).with_suffix('.olean')),str(out/n)]
  start=time.monotonic();p=subprocess.run(cmd,cwd=out,env=env,text=True,capture_output=True);elapsed=time.monotonic()-start
  log=logs/(n+'.log');log.write_text(p.stdout+p.stderr)
  rec={'source':n,'source_sha256':sha(out/n),'command':cmd,'returncode':p.returncode,'seconds':elapsed,'log_sha256':sha(log)}
  records.append(rec)
  if p.returncode or 'sorryAx' in p.stdout+p.stderr:
   (out/'receipt.json').write_text(json.dumps({'status':'FAIL','version':version,'modules':records},indent=2)+'\n')
   raise SystemExit(p.stdout+p.stderr)
  rec['object_sha256']=sha(out/Path(n).with_suffix('.olean'));print(n,'PASS',round(elapsed,3),flush=True)
 receipt={'status':'PASS','version':version,'modules':records,'total_compiler_seconds':sum(x['seconds'] for x in records),'fresh_objects':True,'formal_scope':'Arbitrary-tape finite-window refinement and finite block-chain composition; literal281 decoder blocks and finite234-role conditions. This does not replace full KSim site coverage or the ZFC endpoint.'}
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
