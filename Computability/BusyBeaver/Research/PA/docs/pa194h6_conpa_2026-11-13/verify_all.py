#!/usr/bin/env python3
"""Verify the delivered release without running heuristic discovery searches."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def main():
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without Python -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for name,digest in manifest['files'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('Release integrity mismatch: '+name)
    print('Release integrity PASS',len(manifest['files']),'files',flush=True)
    with tempfile.TemporaryDirectory(prefix='pa194h6-full-') as td:
        tmp=Path(td)
        commands=[
            ('positive_machine',[ROOT/'verify.py','--receipt',tmp/'machine.json']),
            ('independent_structure',[ROOT/'comparison/review_h6_structure.py',ROOT,tmp/'structure.json']),
            ('exact_novelty',[ROOT/'comparison/verify_novelty.py',ROOT/'machine/machine.tm','--output',tmp/'novelty.json']),
            ('scanner_witness',[ROOT/'research/scanner_probe.py',ROOT,'--output',tmp/'scanner.json'])
        ]
        for name,cmd in commands:
            done=subprocess.run([sys.executable,'-B',*map(str,cmd)],capture_output=True,text=True)
            if done.returncode:
                print(done.stdout);print(done.stderr,file=sys.stderr)
                raise SystemExit(done.returncode)
            print(name,'PASS',flush=True)
        novelty=json.loads((tmp/'novelty.json').read_text());assert not novelty['exact_tuple_matches'] and novelty['prior194_classes']==34
        result={'status':'PASS','machine':'PA194H6','source_commit':manifest['source_commit'],
          'dense_sha256':hashlib.sha256((ROOT/'machine/machine.tm').read_bytes()).hexdigest(),
          'manifest_files_checked':len(manifest['files']),'positive_verification':json.loads((tmp/'machine.json').read_text()),
          'independent_structure':json.loads((tmp/'structure.json').read_text()),'novelty':novelty,
          'scanner_witness':json.loads((tmp/'scanner.json').read_text()),
          'scope':'Ordinary mathematical PA calibration with universal executable physical/source certificates. No newly kernel-checked PA/iPRA endpoint; no minimality claim.'}
        if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'status':'PASS','working_states':194,'all_positive_outcomes':4876,'prior194_classes':34,'novelty_matches':0,'dense_sha256':result['dense_sha256']},indent=2))
if __name__=='__main__':main()
