#!/usr/bin/env python3
"""Rebuild and validate the three released machines, offline.

By default, rederive all universal literal contracts for parent and children.
--reuse-checked-contracts reuses previously checked contracts, requiring their
exact input/output hash bindings; the receipt explicitly records this mode.
No search heuristic, external source tree, or Lean installation is required.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
NAMES=('PA194ForestR','PA194ForestB','PA194ForestX')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main(args):
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without -O.')
    before=time.monotonic();commands=[]
    manifest=ROOT/'MANIFEST.sha256.json'
    if manifest.exists():
        inventory=json.loads(manifest.read_text())
        for name,digest in inventory['files'].items():
            assert sha(ROOT/name)==digest,('package identity mismatch',name)
    def run(*arguments):
        command=[sys.executable,'-B',*map(str,arguments)]
        completed=subprocess.run(command,cwd=ROOT,text=True,capture_output=True)
        commands.append({'argv':[str(x)for x in arguments],
                         'returncode':completed.returncode,'stdout':completed.stdout,
                         'stderr':completed.stderr})
        if completed.returncode:
            print(completed.stdout);print(completed.stderr,file=sys.stderr)
            raise AssertionError(('failed verification command',arguments))
        print('PASS',arguments[0],flush=True)
    with tempfile.TemporaryDirectory(prefix='pa194_forest_release_') as temp:
        temp=Path(temp);machines=temp/'machines'
        run('construction/build.py','--output',machines)
        filenames=('machine.tm','machine.native.tm','raw.native.tm','sites.json',
                   'instructions.json','nodes.json','grammar.tree.json','folds.json',
                   'labels.json','macro_bindings.json','local.json','receipt.json')
        for name in NAMES:
            for filename in filenames:
                assert (machines/name/filename).read_bytes()==(ROOT/'machines'/name/filename).read_bytes(),(name,filename)
        parent=temp/'AX11H'
        shutil.copytree(ROOT/'reference/AX11H',parent)
        if args.reuse_checked_contracts:
            for name in NAMES:
                shutil.copytree(ROOT/'machines'/name/'independent',machines/name/'independent')
        else:
            run('verification/check.py',parent,*[machines/name for name in NAMES])
        run('proof/check_clocks.py','--machines',machines,'--parent',parent,
            '--output',temp/'clocks.json')
        novelty_args=['comparison/check_novelty.py','--machines',machines,
                      '--output',temp/'novelty.json']
        if args.recompute_novelty:novelty_args.append('--recompute')
        run(*novelty_args)
        results={'status':'PASS','working_states':194,'machine_count':3,
                 'names':NAMES,'exact_rebuild':True,
                 'literal_verification_mode':('reuse previously checked, hash-bound contracts'
                                             if args.reuse_checked_contracts else 'fresh full literal replay'),
                 'source_and_clock_checks':json.loads((temp/'clocks.json').read_text()),
                 'novelty_checks':json.loads((temp/'novelty.json').read_text()),
                 'seconds':time.monotonic()-before,
                 'commands':commands,'kernel_checked_Lean_endpoint':False}
    output=args.output
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({k:results[k]for k in('status','exact_rebuild','literal_verification_mode','seconds')},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-checked-contracts',action='store_true')
    parser.add_argument('--recompute-novelty',action='store_true')
    parser.add_argument('--output',type=Path,default=ROOT/'verification/release_check.json',
                        help='Write the replay receipt here; defaults to verification/release_check.json.')
    main(parser.parse_args())
