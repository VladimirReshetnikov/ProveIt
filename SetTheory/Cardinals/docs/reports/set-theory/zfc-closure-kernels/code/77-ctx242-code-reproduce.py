#!/usr/bin/env python3
"""Run the documented verification sequence into a fresh output directory."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--expanded',action='store_true')
    args=ap.parse_args()
    out=args.output.resolve()
    if out.exists():raise SystemExit('Choose a fresh output directory.')
    if out==ROOT or ROOT in out.parents:
        raise SystemExit('Choose an output directory outside the source package.')
    out.mkdir(parents=True)
    steps=[
        ('local',['verify_local.py','--out',str(out/'reconstructed')]),
        ('induction',['verify_induction.py','--out',str(out/'induction-audit.json')]),
        ('blank',['verify_blank.py','--out',str(out/'blank-audit.json')]),
        ('literal',['verify_literal.py','--candidate',str(ROOT/'machine'),'--out',str(out)]),
        ('affine',['verify_runtime.py','--out',str(out)]),
    ]
    if args.expanded:steps.append(('expanded',['verify_runtime.py','--expanded','--out',str(out)]))
    records=[]
    for name,argv in steps:
        command=[sys.executable,'-B',str(ROOT/'code'/argv[0]),*argv[1:]]
        print('Running',name,flush=True)
        began=time.monotonic()
        with (out/(name+'.log')).open('w') as log:
            process=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        record={'stage':name,'returncode':process.returncode,'seconds':time.monotonic()-began}
        records.append(record)
        if process.returncode:
            print((out/(name+'.log')).read_text())
            (out/'reproduction.json').write_text(json.dumps({'status':'FAIL','stages':records},indent=2)+'\n')
            raise SystemExit(process.returncode)
    # The generated tables must be the supplied tables byte for byte.
    for name in ('zfc_return_fold242_old.tm','zfc_return_fold242.tm','renumbering.json'):
        assert (out/'reconstructed'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),name
    record={'status':'PASS_ALL_REQUESTED_STAGES','expanded':args.expanded,
            'generated_artifacts_equal_supplied':True,'python':sys.version,
            'stages':records}
    (out/'reproduction.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2),flush=True)

if __name__=='__main__':main()
