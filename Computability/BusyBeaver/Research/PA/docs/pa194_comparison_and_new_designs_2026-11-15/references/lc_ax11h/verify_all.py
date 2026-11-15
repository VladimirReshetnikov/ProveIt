#!/usr/bin/env python3
"""Rebuild PA194LC_AX11H and replay both complete literal implementations."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
EXPECTED='5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--quick',action='store_true',help='Skip physical replays and affine-clock audit, explicitly recording omissions.');a=p.parse_args()
    assert __debug__ and not sys.flags.optimize
    out=(a.output or Path(tempfile.mkdtemp(prefix='pa194lc-ax11h-evidence-'))).resolve();out.mkdir(parents=True,exist_ok=True)
    for name,digest in json.loads((ROOT/'integrity.json').read_text()).items():assert sha(ROOT/name)==digest,name
    stages=[]
    def run(label,args):
        print(label,flush=True)
        r=subprocess.run([sys.executable,'-B',*map(str,args)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(label+'.log')).write_text(r.stdout)
        if r.returncode:print(r.stdout);raise RuntimeError(label+' failed')
        stages.append(label)
    with tempfile.TemporaryDirectory(prefix='pa194lc-ax11h-rebuild-')as temporary:
        work=Path(temporary)
        for name in ['build.py','compiler.py','support.py','symbolic_runtime.py','parent_integrity.json']:shutil.copy2(ROOT/name,work/name)
        shutil.copytree(ROOT/'parent',work/'parent')
        run('build',[work/'build.py',*(['--quick']if a.quick else[])])
        for name in ['machine.tm','machine.native.tm','raw.native.tm','nodes.json','grammar.tree.json','sites.json','instructions.json','labels.json','local.json']:
            assert (ROOT/name).read_bytes()==(work/name).read_bytes(),name
        assert sha(work/'machine.tm')==EXPECTED
        shutil.copy2(work/'receipt.json',out/'build_receipt.json')
        if not a.quick:
            run('independent',[ROOT/'independent/check.py',work,work/'parent','--output',out/'independent'])
            run('durations',[ROOT/'check_durations.py','--evidence',out/'independent','--output',out/'duration_receipt.json'])
    result=dict(status='PASS',family='PA194LC_AX11H',dense_sha256=EXPECTED,stages=stages,physical_replays_executed=not a.quick,relative_ipra_scope='Ordinary computer-assisted proof; no proof-assistant kernel endpoint.',absolute_calibration='Conditional on the separate PA194AX11H calibration.')
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
