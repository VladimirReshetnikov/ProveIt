#!/usr/bin/env python3
"""Rebuild and verify the concrete 245-state certificate using Python only.

The optional --whole-frame pass expands all nine registers and costs several
minutes. The default already proves all 8391 cases with independently derived
universal macro contracts, and checks the exact blank bootstrap twice.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from check_parameterization import check as check_parameterization

ROOT=Path(__file__).resolve().parents[1]
OLD_SHA='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
CANONICAL_SHA='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,help='Fresh replay directory; default is a new temporary directory.')
    ap.add_argument('--whole-frame',action='store_true')
    args=ap.parse_args()
    out=args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc245-replay-'))
    out.mkdir(parents=True,exist_ok=True)
    parameterization=check_parameterization()
    (out/'parameterization.json').write_text(json.dumps(parameterization,indent=2)+'\n')
    manifest=json.loads((ROOT/'manifest.json').read_text())
    for rel,expected in manifest['sha256'].items():
        assert digest(ROOT/rel)==expected,('Artifact hash mismatch',rel)

    def run(name,arguments):
        log=out/(name+'.log')
        with log.open('w') as stream:
            proc=subprocess.run([sys.executable,*map(str,arguments)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
        if proc.returncode:
            raise RuntimeError(log.read_text()[-6000:])

    run('build',[ROOT/'code/build_routing_machine.py',ROOT/'grammar.json',out/'built',
                 '--short-scan','--padding','64','--boot-limit','500000'])
    audit=json.loads((out/'built/machine-audit.json').read_text())
    assert audit['status']=='PASS_AFFINE_AND_BOOT' and audit['working_states']==245
    assert digest(out/'built/machine_old.tm')==OLD_SHA
    assert digest(out/'built/machine.tm')==CANONICAL_SHA
    for name in ['machine.tm','machine_old.tm','sites_logical.json','sites_physical.json','register_bisimulation.json','allocation.json','renumbering.json']:
        assert (out/'built'/name).read_bytes()==(ROOT/'certificate'/name).read_bytes(),name
    run('runtime',[ROOT/'code/audit_existing_machine.py',out/'built/machine_old.tm',out/'built/sites_physical.json',out/'runtime','--padding','64','--boot-limit','500000'])
    runtime=json.loads((out/'runtime/existing-machine-audit.json').read_text())
    assert runtime['status']=='PASS_AFFINE_AND_BOOT'
    assert runtime['macro_inductions']['status']=='PASS'
    assert runtime['affine_all_cases']['cases']==8391
    assert runtime['blank_boot']['blank_steps']==407915
    if args.whole_frame:
        run('whole-frame',[ROOT/'code/full_symbolic_parametric.py','--table',out/'built/machine_old.tm',
                           '--sites',out/'built/sites_physical.json','--all-values','--output',out/'whole-frame.json'])
        whole=json.loads((out/'whole-frame.json').read_text())
        assert whole['status']=='PASS' and whole['complete'] and whole['counts']['cases']==8391
    result=dict(status='PASS_245_CERTIFICATE',working_states=245,binary_rows=490,
        canonical_sha256=CANONICAL_SHA,old_label_sha256=OLD_SHA,
        grammar_rules=128,remaining_framework_states=117,
        source_bisimulation=audit['register_program_bisimulation'],
        parameterization='Exact text equality after the declared parameter/import changes',
        actual_table_macro_inductions='PASS',all_affine_cases=8391,frame_padding=64,
        exact_blank_steps=407915,initial_header_distance=181,
        independently_replayed_whole_frame=args.whole_frame,
        proof_status='Ordinary mathematical certificate; no new proof-assistant kernel endpoint.',
        output=str(out))
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
