#!/usr/bin/env python3
"""Copy this packet and reconstruct/replay its exact MP194 construction."""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parent
def main():
    assert __debug__,'Run with assertions enabled'
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--quick',action='store_true',help='reuse the supplied direct-runtime certificate; rerun all other checks')
    a=p.parse_args();out=a.output.resolve()
    assert not out.exists(),'Choose a fresh output directory'
    assert out!=ROOT and ROOT not in out.parents,'Output must be outside this packet'
    shutil.copytree(ROOT,out,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    def run(script,*args):subprocess.run([sys.executable,str(out/'code'/script),*map(str,args)],check=True,env=env)
    C=out/'candidate';R=out/'reference';V=out/'verification'
    run('build.py')
    run('check_mp_source_closure.py','--parent',R,'--child',C,'--output',V/'replayed_source_closure.json')
    run('check_mp194_startup.py',C/'machine.native.tm',C/'sites.json','--output',V/'replayed_startup.json')
    if not a.quick:
        fresh=V/'replayed_runtime'
        run('check_physical.py',C/'machine.native.tm',C/'sites.json','--output',fresh)
        for n in['contracts.json','list_lemmas.json']:
            assert(fresh/n).read_bytes()==(V/'runtime'/n).read_bytes(),n
        old=json.loads((V/'runtime/receipt.json').read_text());new=json.loads((fresh/'receipt.json').read_text())
        assert{k:v for k,v in old.items()if k!='seconds'}=={k:v for k,v in new.items()if k!='seconds'}
    run('check_mp_clocks.py','--parent-contracts',R/'contracts.json','--child-contracts',V/'runtime/contracts.json','--output',V/'replayed_clock_bounds.json')
    result={'status':'PASS','runtime_freshly_replayed':not a.quick,
      'scope':'Exact reconstruction, source closure, whole-tape blank startup and coefficient audit; fresh full direct runtime unless --quick. Uniform mathematical rule soundness and the exact parent calibration remain identified proof dependencies.'}
    (V/'reproduction.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
