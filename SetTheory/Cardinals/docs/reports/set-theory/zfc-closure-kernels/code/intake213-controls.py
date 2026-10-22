#!/usr/bin/env python3
"""Own bounded negative controls for the inert supplemental213 recovery helper."""
import argparse, copy, hashlib, json
from pathlib import Path
import subprocess, sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--helper',type=Path,required=True)
    ap.add_argument('--map',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();a.out.mkdir(exist_ok=False)
    original=a.map.read_bytes();m=json.loads(original)
    trials=[]
    bad=copy.deepcopy(m);bad['members'][0]['sha256']='0'*64
    trials.append(('changed-sha',bad,'Member bytes changed:'))
    bad=copy.deepcopy(m);bad['members'].pop(0)
    trials.append(('missing-member',bad,'Missing/reordered map member'))
    bad=copy.deepcopy(m);r=bad['members'][0]
    other=next(v for v in bad['members'] if v['route']=='git' and v['path']!=r['path'])
    r['path']=other['path'];r['commit']=other['commit']
    trials.append(('wrong-alias',bad,'Member bytes changed:'))
    result=[]
    for name,bad,expect in trials:
        path=a.out/(name+'.json');path.write_text(json.dumps(bad,indent=2)+'\n')
        cmd=[sys.executable,str(a.helper),'--repo',str(a.repo),'--map',str(path),'--verify-only']
        run=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
        (a.out/(name+'.stdout.txt')).write_bytes(run.stdout)
        assert run.returncode!=0 and expect in run.stdout.decode(),(name,run.returncode,run.stdout)
        result.append({'control':name,'expected_rejection':expect,'returncode':run.returncode,
                       'argv':cmd,'log_sha256':hashlib.sha256(run.stdout).hexdigest()})
    assert a.map.read_bytes()==original
    out={'status':'PASS_THREE_EXPECTED_REJECTIONS','map_sha256':hashlib.sha256(original).hexdigest(),
         'helper_sha256':hashlib.sha256(a.helper.read_bytes()).hexdigest(),'controls':result,
         'supplied_code_or_compiler_executed':False,'original_map_unchanged':True}
    (a.out/'result.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
