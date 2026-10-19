#!/usr/bin/env python3
"""Regenerate finite literal instruction fixtures for six Context246 layouts.

--domain unrestricted reproduces the former 8391-case corpus exactly.
--domain guards deletes just the six infeasible source guards (8385 cases).
--domain product creates four concrete files per feasible guard, each satisfying
all nine source masks and the selected decrement guard (33540 cases). This is
finite evidence, not exhaustive enumeration of the product invariant domain.
"""
import argparse
import hashlib
import json
from pathlib import Path
from common import CERTIFICATE, EXCLUDED, LAYOUTS, PHYSICAL, L, inputs, guarded_sites
from admissible_guards import verify_transport
from product_verifier import possibilities


def registers(op, arg, zero, masks, suite):
    if masks is None:
        physical = [(i * 3 + 1) % 5 for i in range(9)]
        if op == 'CD':
            physical[PHYSICAL[arg]] = 0 if zero else 2
        return physical
    physical = [0] * 9
    for logical, mask in enumerate(masks):
        if op == 'CD' and logical == arg:
            mask &= 1 if zero else 6
        allowed = possibilities(mask)
        if suite == 0:
            category = min(allowed)
        elif suite == 1:
            category = max(allowed)
        elif suite == 2:
            category = allowed[(logical + 1) % len(allowed)]
        else:
            assert suite == 3
            category = allowed[(logical + 2) % len(allowed)]
        value = category if category < 2 else 2 + (suite == 3)
        assert mask & (1 << min(value, 2))
        physical[PHYSICAL[logical]] = value
    return physical


def generate(layout, domain):
    sites, table = inputs(layout)
    masks = json.loads(CERTIFICATE.read_text())['masks']
    result = [str(len(table))]
    for (q, bit), (write, direction, target) in sorted(table.items()):
        result.append(f'{q} {bit} {write} {direction} {target}')
    cases = []
    rejected_old_fixtures = 0
    for index, site, pc, op, arg, zero in guarded_sites(sites):
        if domain != 'unrestricted' and index in EXCLUDED:
            continue
        if index not in EXCLUDED:
            old = registers(op, arg, zero, None, 0)
            rejected_old_fixtures += any(
                not mask & (1 << min(old[PHYSICAL[r]], 2))
                for r, mask in enumerate(masks[site]))
        for suite in range(4 if domain == 'product' else 1):
            values = registers(op, arg, zero, masks[site] if domain == 'product' else None, suite)
            spares = [0, 2]
            source = sorted(L.paint(pc, 40, values, spares, 0))
            expected = L.expected(pc, op, arg, values, spares, 0, 40)
            head = 0 if expected is None else expected[0]
            target = [] if expected is None else sorted(expected[1])
            cases.append(' '.join(map(str, [int(op == 'CH'), head, len(source),
                *source, len(target), *target])))
    assert len(cases) == {'unrestricted': 8391, 'guards': 8385, 'product': 33540}[domain]
    result += [str(len(cases))] + cases
    content = '\n'.join(result) + '\n'
    return content, dict(layout=str(layout), domain=domain, instruction_cases=len(cases),
        guarded_cases=8391 if domain == 'unrestricted' else 8385,
        suites_per_guard=4 if domain == 'product' else 1, table_states=246,
        excluded_case_indices=[] if domain == 'unrestricted' else list(EXCLUDED),
        old_guard_restricted_fixtures_violating_product=rejected_old_fixtures,
        fixture_sha256=hashlib.sha256(content.encode()).hexdigest(), finite_only=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('layout', choices=LAYOUTS)
    parser.add_argument('--domain', choices=('unrestricted', 'guards', 'product'), default='unrestricted')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    verify_transport((args.layout,))
    content, metadata = generate(args.layout, args.domain)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content)
    args.output.with_suffix('.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(metadata))


if __name__ == '__main__':
    main()
