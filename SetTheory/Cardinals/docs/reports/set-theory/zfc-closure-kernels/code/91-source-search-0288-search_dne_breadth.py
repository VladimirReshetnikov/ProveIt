#!/usr/bin/env python3
"""A bounded screen of all 63 nonidentity DNE normalizations.

Discovery is timed and stochastic. Every saved proposal is checked by the
independent exact grammar auditor; grammar success is not a full TM theorem.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--seconds', type=float, default=5)
    p.add_argument('--seeds', type=Path, required=True)
    p.add_argument('--runtime', type=Path, required=True)
    p.add_argument('--executable', type=Path, required=True)
    p.add_argument('--locks', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    sys.path.insert(0, str(args.runtime.resolve() / 'code'))
    from audit_fine_grammar import audit
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for mask in range(1, 64):
        seed_dir = args.seeds / f'mask{mask:02d}'
        seed = json.loads((seed_dir / 'seed.json').read_text())
        out = args.output / f'mask{mask:02d}'
        out.mkdir(exist_ok=True)
        proposal = out / 'candidate.json'
        command = [str(args.executable.resolve()), str(seed_dir / 'grammar.txt'),
                   str(seed_dir / 'constraints.txt'), str(proposal),
                   str(args.seconds), str(2026101800 + mask), '127',
                   str(args.locks), str(seed_dir / 'resume.txt')]
        t0 = time.monotonic()
        with (out / 'search.log').open('w') as log:
            proc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        record = dict(mask=mask, command=command, returncode=proc.returncode,
                      elapsed_seconds=time.monotonic()-t0,
                      initial_rules=seed['rules_count'])
        if proc.returncode == 0 and proposal.exists():
            data = json.loads(proposal.read_text())
            data['source_override'] = seed['source_override']
            data['source_variant'] = seed.get('source_variant', {})
            data['short_scan'] = True
            data['status'] = 'GRAMMAR_PROPOSAL_REQUIRES_RUNTIME_AND_LOGIC_CHECKS'
            proposal.write_text(json.dumps(data, indent=2) + '\n')
            try:
                report = audit(proposal, short_scan=True)
                (out / 'grammar-audit.json').write_text(json.dumps(report, indent=2)+'\n')
                record.update(status=report['status'], rules=data['rules_count'],
                              working_states=report['working_states'],
                              properties=data['properties'], iterations=data['iterations'])
            except Exception as exc:
                record.update(status='AUDIT_FAILED', error=repr(exc))
        else:
            record['status'] = 'SEARCH_FAILED'
        results.append(record)
        print(json.dumps(record), flush=True)
        (args.output / 'summary.json').write_text(json.dumps(dict(
            scope='Timed proposal search plus exact grammar checks; no negative lower bound.',
            seconds_per_mask=args.seconds, results=results), indent=2)+'\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
