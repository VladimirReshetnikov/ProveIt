#!/usr/bin/env python3
"""Replay the two new finite obstructions against the attributed 246 table.

Default layout: package_root/baseline246/zfc-context246 and
package_root/portable/verify_audit.py. No dependency downloads or proof-
assistant compilation. Output is written outside the baseline directory.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path,
                    default=here.parent/'baseline246'/'zfc-context246')
    ap.add_argument('--output', type=Path, default=here/'replay-output')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    table = args.baseline/'machine'/'zfc_prefix246_old.tm'
    program = args.baseline/'sources'/'Prog254.v'
    jobs = [('probe_state204_safe_phase.py', 'state204_safe_phase_probe.json'),
            ('probe_short_detector_d181.py', 'short_detector_d181.json')]
    for script, artifact in jobs:
        result = subprocess.run([sys.executable, '-B', str(here/script),
            '--table', str(table), '--program', str(program),
            '--output', str(args.output/artifact)], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode:
            print(result.stdout, end='')
            print(result.stderr, end='', file=sys.stderr)
            raise SystemExit(result.returncode)
    phase = json.loads((args.output/'state204_safe_phase_probe.json').read_text())
    detector = json.loads((args.output/'short_detector_d181.json').read_text())
    summary = {'status': 'PASS', 'scope': 'Finite prepared-tape obstructions only',
        'source_register_steps_after_fetch': phase['source_phase_certificate']['literal_register_steps_after_fetch'],
        'state204_small_phase_halt_steps': phase['steps'],
        'state204_large_phase_halt_steps': phase['stronger_resources_control']['steps'],
        'detector_baseline_exact_endpoint_steps': detector['baseline']['steps'],
        'detector_false_dispatches': [
            {'states': 246-len(c['deleted_states']), 'steps': c['steps'], 'head': c['head']}
            for c in detector['counterexamples']],
        'all_final_tapes_checked_independently': True,
        'new_sub246_consistency_machine_claimed': False}
    (args.output/'verification-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
