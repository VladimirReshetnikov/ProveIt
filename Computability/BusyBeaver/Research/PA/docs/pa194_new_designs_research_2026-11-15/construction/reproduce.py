#!/usr/bin/env python3
"""Rebuild the candidate and independently recheck every new finite premise."""
import argparse,json,subprocess,sys,tempfile,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    out=(a.output or Path(tempfile.mkdtemp(prefix='pa194-lcsf3-replay-'))).resolve();out.mkdir(parents=True,exist_ok=True)
    for label,args in [('build',[ROOT/'build.py','--output',out/'candidate']),('verify',[ROOT/'verify.py','--candidate',out/'candidate','--output',out/'verification.json'])]:
        r=subprocess.run([sys.executable,'-B',*map(str,args)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(label+'.log')).write_text(r.stdout)
        if r.returncode:print(r.stdout);raise RuntimeError(label+' failed')
    inherited=out/'inherited_composites';shutil.copytree(ROOT/'reference/composites',inherited,dirs_exist_ok=True)
    r=subprocess.run([sys.executable,'-B',str(inherited/'verify_composites.py')],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/'inherited_sf.log').write_text(r.stdout)
    if r.returncode:print(r.stdout);raise RuntimeError('inherited SF finite-premise replay failed')
    result={'status':'PASS','candidate_directory':str(out/'candidate'),'new_finite_premises_replayed':True,'inherited_sf_finite_premises_replayed':True,'proof_assistant_kernel_checked':False}
    (out/'reproduction.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
