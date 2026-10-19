#!/usr/bin/env python3
"""Regenerate the finite theory and codec evidence on a disposable copy.

No unbounded refutation or binary state search is invoked. Exceptions and
failed subprocesses remain failures; they are never mathematical refutations.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    if out.exists():
        ap.error('--output must be a new directory')
    out.mkdir(parents=True)
    theory = out/'theory'
    shutil.copytree(root/'theory', theory)
    commands = [
        ['frozen_kernel.py'],
        ['frozen_frontend.py', '--stage', '1'],
        ['frozen_frontend.py', '--stage', '1', '--extensional',
         '--output', 'frozen-frontend-extensional-results.json'],
        ['boolean_class_control.py'],
        ['linear_ground_codec.py'],
        ['linear_ground_codec.py', '--boolean-normalized',
         '--output', 'linear-ground-boolean-results.json'],
        ['shared_template_codec.py'],
        ['named_selector.py'],
        ['channel_collapse_control.py'],
        [str(root/'code/codec_audit.py'), '--formalisms', str(theory),
         '--output', str(out/'independent-codec-review.json')],
    ]
    records = []
    began = time.monotonic()
    for i, arguments in enumerate(commands):
        log = out/(str(i+1).zfill(2)+'-'+Path(arguments[0]).stem+'.log')
        start = time.monotonic()
        with log.open('w') as stream:
            subprocess.run([sys.executable, '-B', *arguments], cwd=theory,
                           stdout=stream, stderr=subprocess.STDOUT,
                           check=True, timeout=180)
        records.append(dict(program=Path(arguments[0]).name, arguments=arguments[1:],
                            seconds=round(time.monotonic()-start, 6), log=log.name))
        print('PASS '+Path(arguments[0]).name, flush=True)
    audit = json.loads((out/'independent-codec-review.json').read_text())
    assert audit['status'] == 'PASS' and audit['shared_cases'] == 78
    assert len(audit['independently_grounded_counts']) == 12
    summary = dict(status='PASS_FINITE_THEORY_AND_ENCODING_REPRODUCTION',
                   independent_shared_cases=78, independent_ground_comparisons=12,
                   commands=records, seconds=round(time.monotonic()-began, 6),
                   scope='Finite codec/transcription checks; ordinary proofs are in the report. No binary TM state claim.')
    (out/'reproduction-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'commands'}, indent=2))


if __name__ == '__main__':
    main()
