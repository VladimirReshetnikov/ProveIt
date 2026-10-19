#!/usr/bin/env python3
"""Replay the 237 endpoint: complete 238 proof, then all-tape 237 transfer.

--quick omits a fresh unbounded 238 runtime execution, as explicitly reported.
The 237 endpoint is proved through exact positive-block simulation. A fresh
direct unbounded 237 runtime run is not claimed by this driver.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    require(__debug__ and not sys.flags.optimize,'Run without -O or -OO')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--with-guard',action='store_true')
    args=parser.parse_args();out=args.output.resolve()
    require(out!=ROOT and ROOT not in out.parents,'Output must be outside the package')
    require(not out.exists() or not any(out.iterdir()),'Output must be new or empty')
    out.mkdir(parents=True,exist_ok=True);began=time.monotonic()
    if (ROOT/'MANIFEST.sha256').exists():
        for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
            digest,name=line.split('  ',1);p=(ROOT/name).resolve()
            require(ROOT in p.parents and sha(p)==digest,'Manifest mismatch '+name)
    env=dict(os.environ)
    for key in ('PYTHONPATH','PYTHONOPTIMIZE','B245_INPUTS','B245_OUTPUT'):env.pop(key,None)
    def run(name,command,receipt,status):
        with (out/(name+'.log')).open('w') as log:
            subprocess.run([sys.executable,'-B',*map(str,command)],cwd=ROOT,env=env,
                stdout=log,stderr=subprocess.STDOUT,check=True,timeout=1200)
        data=json.loads(receipt.read_text());require(data['status']==status,'Wrong '+name+' status')
        print(name,status,flush=True);return data
    core=ROOT/'composition238'
    command=[core/'reproduce.py','--output',out/'composition238']
    if args.quick:command.append('--quick')
    if args.with_guard:command.append('--with-guard')
    parent=run('composition238',command,out/'composition238/replay.json',
        'QUICK_REPLAY_PASS' if args.quick else 'FULL_238_MATHEMATICAL_REPLAY_PASS')
    generated=out/'built237';generated.mkdir()
    local=run('local237',[ROOT/'verification/certify_extension237.py','--old',core/'machines/zfc_composed238_old.tm',
        '--new',generated/'zfc_extended237_old.tm','--build','--output',out/'local237.json'],
        out/'local237.json','EXACT237_ALL_INITIAL_TAPE_BLOCK_SIMULATION_PASS')
    for name in ('zfc_extended237_old.tm','zfc_extended237.tm','renumbering237.json'):
        require((generated/name).read_bytes()==(ROOT/'machines'/name).read_bytes(),'Reconstruction mismatch '+name)
    boot=run('bootstrap237',[ROOT/'verification/check_bootstrap237.py','--old',core/'machines/zfc_composed238_old.tm',
        '--new',ROOT/'machines/zfc_extended237_old.tm','--baseline-receipt',out/'composition238/bootstrap238.json',
        '--output',out/'bootstrap237.json'],out/'bootstrap237.json','EXACT237_UNCHANGED_WHOLE_TAPE_BOOTSTRAP_PASS')
    result={'status':'QUICK_237_TRANSFER_REPLAY_PASS' if args.quick else 'FULL_237_MATHEMATICAL_TRANSFER_REPLAY_PASS',
        'canonical237_sha256':sha(ROOT/'machines/zfc_extended237.tm'),
        'fresh_238_runtime_replayed':not args.quick,'fresh_237_local_transfer_replayed':True,
        'fresh_direct_237_runtime_replayed':False,'inherited_calibration_rebuilt':False,
        'new_kernel_endpoint_rebuilt':False,'startup_steps':boot['steps'],
        'all_old_rows_in_transfer':local['complete_old_row_coverage'],
        'parent_receipt_sha256':sha(out/'composition238/replay.json'),
        'local_receipt_sha256':sha(out/'local237.json'),'bootstrap_receipt_sha256':sha(out/'bootstrap237.json'),
        'seconds':time.monotonic()-began}
    (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
