#!/usr/bin/env python3
"""Replay PA194H5's finite construction and independent physical certificates.

Python 3.10+ standard library only. Run without -O. This is not an
end-to-end proof-assistant verification of the ordinary PA theorem.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
EXPECTED = '417e3940a77a6222ccd06885209cc853e572ac48b64acbabf581942f142304c9'

def main():
    assert __debug__ and not sys.flags.optimize
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'verification/replay.json')
    parser.add_argument('--frontier',type=Path,help='Optional directory of frozen 194-state comparison tables')
    args = parser.parse_args()
    def run(*argv):
        subprocess.run([sys.executable,*map(str,argv)],check=True,cwd=ROOT)
    with tempfile.TemporaryDirectory(prefix='pa194h5_replay_') as temp:
        temp=Path(temp); machine=temp/'machine'
        run(ROOT/'construction/build_h5.py','--output',machine)
        for name in ['machine.tm','machine.native.tm','raw.native.tm','sites.json',
                     'instructions.json','nodes.json','folds.json','labels.json']:
            assert (machine/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),name
        assert hashlib.sha256((machine/'machine.tm').read_bytes()).hexdigest()==EXPECTED
        run(ROOT/'verification/check.py',machine)
        run(ROOT/'proof/check_source_binding.py','--output',temp/'source_binding.json')
        run(ROOT/'proof/check_commands.py','--output',temp/'commands.json')
        summary = {
            'family':'PA194H5', 'status':'PASS', 'rebuild_matches_packaged_artifacts':True,
            'construction':json.loads((machine/'receipt.json').read_text()),
            'independent_runtime':json.loads((machine/'independent/receipt.json').read_text()),
            'source_binding':json.loads((temp/'source_binding.json').read_text()),
            'emitter_and_words':json.loads((temp/'commands.json').read_text()),
            'kernel_checked':False,
            'scope':'Executable universal source/tape certificates and exact symbolic command identities. The PA biconditional uses the separately supplied ordinary mathematical calibration.'
        }
        if args.frontier:
            run(ROOT/'verification/verify_novelty.py',machine/'machine.tm',args.frontier,'--output',temp/'novelty.json')
            summary['novelty']=json.loads((temp/'novelty.json').read_text())
            assert summary['novelty']['structurally_new']
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps({'family':'PA194H5','status':'PASS','dense_sha256':EXPECTED,'receipt':str(args.output)}))

if __name__=='__main__': main()
