#!/usr/bin/env python3
"""Replay PA194GAX11 checks in a temporary copy; preserve frozen artifacts."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
EXPECTED='7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--quick',action='store_true',help='Skip both physical replays, recording that omission.')
    args=parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions must be enabled.')
    output=(args.output or Path(tempfile.mkdtemp(prefix='gax11-evidence-'))).resolve()
    output.mkdir(parents=True,exist_ok=True)
    integrity=json.loads((ROOT/'integrity.json').read_text())
    for name,digest in integrity.items():
        if sha(ROOT/name)!=digest:raise ValueError('Input integrity mismatch: '+name)
    stages=[]
    def run(label,argv):
        print(label,flush=True)
        result=subprocess.run([sys.executable,'-B',*map(str,argv)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (output/(label+'.log')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout)
            raise RuntimeError(label+' failed')
        stages.append(label)
    with tempfile.TemporaryDirectory(prefix='gax11-rebuild-')as temporary:
        work=Path(temporary)
        for name in ['build_new.py','compiler.py','support.py','symbolic_runtime.py','baseline.raw.native.tm','nodes.json','grammar.json','folds.json']:
            shutil.copy2(ROOT/name,work/name)
        run('build',[work/'build_new.py',*(['--quick']if args.quick else[])])
        for name in ['machine.tm','machine.native.tm','raw.native.tm','grammar.new.json','grammar.tree.json','sites.json','instructions.json','labels.json','local.json']:
            if (ROOT/name).read_bytes()!=(work/name).read_bytes():raise ValueError('Reconstruction mismatch: '+name)
        if sha(work/'machine.tm')!=EXPECTED:raise ValueError('Wrong dense table')
        shutil.copy2(work/'receipt.json',output/'build_receipt.json')
        shutil.copy2(ROOT/'nodes.json',work/'nodes.json')
        run('commands',[ROOT/'check_commands_new.py','--machine',work,'--output',output/'commands_receipt.json'])
        if not args.quick:
            run('independent',[ROOT/'independent/check.py',work,'--output',output/'independent'])
    receipt={'status':'PASS','family':'PA194GAX11','dense_sha256':EXPECTED,'stages':stages,'physical_replays_executed':not args.quick,'frozen_outputs_preserved':True,'claim':'Reconstruction and symbolic implementation evidence, not an absolute iPRA consistency theorem.'}
    (output/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2));print('Evidence directory:',output)

if __name__=='__main__':main()
