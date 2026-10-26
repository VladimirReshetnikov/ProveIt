#!/usr/bin/env python3
"""Regenerate the pinned LTE patch and transparent source-count metrics."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
RELATIVE = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/PrimePowerOrder.lean')
BASELINE_HASH = '781aa36c18153b4f7e7e6b7df204b3b42545bc8cabf0f9f25736d012e598dd47'


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def signatures(text):
    return {m[1]: text[m.start():].split(':=', 1)[0]
            for m in re.finditer(r'^theorem (\w+)', text, re.M)}


def proof_lines(text, name):
    block = text[text.index('theorem ' + name):].split('\n\n', 1)[0]
    return len(block.split(':= by\n', 1)[1].splitlines())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path)
    args = parser.parse_args()
    before = (args.repo / RELATIVE).read_text()
    if digest(before) != BASELINE_HASH:
        raise SystemExit('Baseline file differs from the reviewed snapshot; refusing misleading counts.')
    after = (HERE / 'candidate/DiophantineConsistency/PrimePowerOrder.lean').read_text()
    patch = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                      fromfile='a/' + str(RELATIVE), tofile='b/' + str(RELATIVE)))
    (HERE / 'prime-power-spectrum.patch').write_text(patch)
    old, new = signatures(before), signatures(after)
    metrics = {
        'snapshot': '9f35798db4a63c25e435fca14d75931144657d7e',
        'source_path': str(RELATIVE),
        'baseline_sha256': digest(before), 'candidate_sha256': digest(after),
        'baseline_physical_lines': len(before.splitlines()),
        'candidate_physical_lines': len(after.splitlines()),
        'net_physical_lines_removed': len(before.splitlines()) - len(after.splitlines()),
        'proof_body_lines': {name: {'before': proof_lines(before, name),
                                    'after': proof_lines(after, name)}
                             for name in ['exact_lift', 'order_succ']},
        'new_helper_body_lines': proof_lines(after, 'lift_dvd_iff'),
        'existing_types_textually_identical': {name: old[name] == new.get(name) for name in old},
        'extra_theorems': sorted(set(new) - set(old)),
        'counting_note': 'Whole-module counts include the complete added helper, its statement, and comments. Test/prototype files are not imported by this production patch.'
    }
    (HERE / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps(metrics, indent=2))


if __name__ == '__main__':
    main()
