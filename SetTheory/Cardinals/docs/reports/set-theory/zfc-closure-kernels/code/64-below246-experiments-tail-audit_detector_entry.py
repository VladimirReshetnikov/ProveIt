#!/usr/bin/env python3
"""Check all universal Context246 state6-entry cylinders.

This augments the inherited affine execution with assertions only. It proves
the finite input partition needed by the proposed eight-state detector at
every symbolic entry in all 8,391 instruction contracts. As with the inherited
checker, the oracle contracts are ordinary symbolic-induction dependencies.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import inspect
import json
import os
import sys


def main():
    package_root = Path(__file__).resolve().parents[2]
    default_base = package_root / 'baseline/context246'
    if not default_base.exists():
        default_base = package_root / 'context246/zfc-context246'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', type=Path, default=Path(os.environ.get('ZFC246_BASE', default_base)))
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('detector-entry-audit.json'))
    args = ap.parse_args()
    if not __debug__:
        raise SystemExit('Assertions must be enabled.')
    os.environ['ZFC246_BASE'] = str(args.base.resolve())
    os.environ['ZFC246_TABLE'] = str(args.base.resolve() / 'machine/zfc_prefix246_old.tm')
    sys.dont_write_bytecode = True
    loader = Path(__file__).resolve().parents[1] / 'decoder/fold_search246.py'
    if not loader.exists():
        loader = Path(__file__).resolve().parents[1] / 'decoder_reduction/fold_search246.py'
    spec = importlib.util.spec_from_file_location('detector_entry_context', loader)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    assert hashlib.sha256(m.TABLE.read_bytes()).hexdigest() == '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
    counts = Counter()
    sites = Counter()

    def first_known_bits(segs, number, blank_after=False):
        answer = []
        for seg in segs:
            if seg[0] == 'b':
                answer.append(seg[1])
            elif seg[0] == 'r':
                _, bit, coefficient, constant = seg
                answer.extend([bit] * min(number - len(answer), constant))
                if len(answer) < number and coefficient:
                    # A positive unary block may have arbitrary extra cells;
                    # only the first one is needed to close a short cylinder.
                    return answer, 'unknown_nonnegative_extension'
            elif seg[0] == 'box':
                kind, data = seg[1]
                assert kind in ('plain', 'mark')
                answer.extend([0, 0 if kind == 'mark' and data == 0 else 1])
                return answer[:number], 'opaque_box'
            else:
                raise AssertionError(('unknown symbolic segment', seg))
            if len(answer) >= number:
                return answer[:number], 'known_prefix'
            if 1 in answer:
                # Beyond the first one there is no additional premise on the
                # left exterior for a short detector cylinder.
                return answer, 'first_one'
        if blank_after:
            answer.extend([0] * (number - len(answer)))
        return answer[:number], 'blank_exterior' if blank_after else 'end'

    active = None

    def entry_hook(onleft, left, right):
        assert onleft, ('unexpected entry orientation', active)
        rb, _ = first_known_bits(right, 2)
        assert rb == [0, 1], ('right entry guard failed', active, right)
        lb, reason = first_known_bits(left, 9, blank_after=True)
        if 1 in lb:
            k = lb.index(1)
            assert k <= 7, ('excluded first-left-one at distance eight', active, left)
            label = f'short_{k}'
        else:
            assert lb == [0] * 9, ('long cylinder has insufficient known zeros', active, left, lb, reason)
            label = 'long_at_least_nine_known_zeros'
        counts[label] += 1
        sites[active] += 1

    source = inspect.getsource(m.A.run)
    needle = '    for _ in range(fuel):\n'
    assert source.count(needle) == 1
    augmented = source.replace(needle,
        '    entry_seen = False\n'
        '    for _ in range(fuel):\n'
        '        if q == "6" and not entry_seen:\n'
        '            detector_entry_hook(onleft, left, right)\n'
        '        entry_seen = (q == "6")\n')
    m.A.__dict__['detector_entry_hook'] = entry_hook
    exec(augmented, m.A.__dict__)
    for i, case in enumerate(m.CASES):
        active = i
        okay, _, reason = m.check(m.T, i, 1000)
        assert okay, ('instruction failed', i, case[:4], reason)
    output = dict(
        status='PASS', instruction_cases=len(m.CASES),
        instruction_cases_with_entry=len(sites), entries=sum(counts.values()),
        input_partition=dict(sorted(counts.items())),
        exact_baseline_sha256=hashlib.sha256(m.TABLE.read_bytes()).hexdigest(),
        inherited_affine_source_sha256=hashlib.sha256((args.base/'sources/prior/prefix_affine.py').read_bytes()).hexdigest(),
        unchanged_induction_support_rows=len(m.P),
        entry_guard='At state6, tape(+1)=0 and tape(+2)=1. Either the first leftward1 is at distance0..7, or every cell -8..0 is known0.',
        scope='All arbitrary-parameter instruction frames covered by the inherited affine and register-induction proof. Blank startup remains a separate finite check.',
        proof_status='Ordinary exact symbolic execution with checked unary/list induction dependencies; no new proof-assistant kernel theorem.')
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
