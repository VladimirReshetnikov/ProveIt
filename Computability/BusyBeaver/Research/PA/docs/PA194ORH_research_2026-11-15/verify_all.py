#!/usr/bin/env python3
"""Rebuild and verify the delivered machines using only bundled Python files.

The finite checks support the written proofs; this is not a Lean proof
compiler and does not kernel-check the absolute PA calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'PA194ORH': 'c16bef7a1587e31adaae747d5bad26721f30bb5c6c33dd4b798be95f5141f1d4',
    'PA194OR': '379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(script, *args):
    command = [sys.executable, '-B', str(ROOT/script), *map(str,args)]
    print('Checking '+script, flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise SystemExit(result.returncode)
    return result.stdout

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT/'verification/release_check.json')
    ap.add_argument('--recompute-novelty', action='store_true',
                    help='Recompute every corpus canonical form instead of verified cached forms.')
    args = ap.parse_args()
    begin = time.monotonic()
    receipts = {}
    assert __debug__, 'Run without -O; checks use assertions.'
    with tempfile.TemporaryDirectory(prefix='pa194or_verify_') as tmp:
        tmp = Path(tmp)
        for name, script in [('PA194ORH','construction/build.py'),
                             ('PA194OR','construction/build_or.py')]:
            built = tmp/name
            run(script, '--output', built)
            frozen = ROOT/'machines'/name
            assert sha(built/'machine.tm') == EXPECTED[name] == sha(frozen/'machine.tm')
            for f in ['machine.native.tm','raw.native.tm','parent.tm','parent.native.tm',
                      'nodes.json','sites.json','instructions.json','labels.json','folds.json',
                      'parent.sites.json','parent.instructions.json']:
                assert (built/f).read_bytes() == (frozen/f).read_bytes(), (name,f)
            run('verification/check.py', built)
            got = json.loads((built/'independent/receipt.json').read_text())
            old = json.loads((frozen/'independent/receipt.json').read_text())
            for k in ['status','states','rows','source_sites','source_outcomes','startup_steps',
                      'dense_sha256','native_sha256','contracts_sha256','box_oracles']:
                assert got[k] == old[k], (name,k,got[k],old[k])
            assert got['status']=='PASS' and got['box_oracles'] is False
            novelty = tmp/(name+'_novelty.json')
            more = ['--recompute'] if args.recompute_novelty else []
            run('comparison/check_novelty.py', built/'machine.tm', '--output', novelty, *more)
            nr = json.loads(novelty.read_text())
            assert nr['structurally_new'] and nr['compared_spanning_classes']==520
            assert not nr['matches']
            nr['candidate'] = str((frozen/'machine.tm').relative_to(ROOT))
            receipts[name] = {'dense_sha256':EXPECTED[name],
                              'independent':got,'novelty':nr}
        assert receipts['PA194ORH']['novelty']['broad_graph'] != receipts['PA194OR']['novelty']['broad_graph']
        relative = tmp/'relative.json'
        run('proof/relative_ORH_check.py', '--candidate', tmp/'PA194ORH', '--output', relative)
        relation = json.loads(relative.read_text())
        assert relation['status']=='PASS' and relation['source_instruction_arrays_identical']
        run('research/engine/relative_OR_check.py', '--candidate', tmp/'PA194OR',
            '--output', tmp/'secondary_relative.json')
        secondary_relation = json.loads((tmp/'secondary_relative.json').read_text())
        assert secondary_relation['status']=='PASS' and secondary_relation['source_instruction_arrays_identical']
        audit = tmp/'audit.json'
        run('research/logic/ORH_audit.py', '--packet', tmp/'PA194ORH', '--output', audit)
        run('research/logic/mp_tail_words.py')
        run('research/engine/check_rejected.py')
        receipt = {'status':'PASS','machines':receipts,
                   'relative_ORH':relation,'relative_OR':secondary_relation,
                   'scope':'Deterministic rebuild, literal universal certificates, exact source/local audits, structural novelty, command-word algebra and expected rejection examples. Written arithmetic proof separate; no new Lean endpoint.',
                   'elapsed_seconds':round(time.monotonic()-begin,3)}
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','machines':list(EXPECTED),
                      'elapsed_seconds':receipt['elapsed_seconds'],
                      'receipt':str(args.output)},indent=2),flush=True)

if __name__=='__main__':
    main()
