#!/usr/bin/env python3
"""Emit the unscaled reduced-auxiliary circuit from the pinned P67 source."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DEST = ROOT / 'Computability/DiophantineConsistency/circuits/p69_unscaled.json'
SOURCE = ROOT / ('Computability/DiophantineConsistency/'
                 'con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json')


def build():
    original = json.loads(SOURCE.read_text())
    gates = []
    for name, operation, left, right in original['source']:
        if name == 'aux_coefficient_root':
            right = 'c2'
        elif name == 'scaled_f_square':
            name, right = 'strong_square_scaled', 'R16'
        elif name == 'norm_strong':
            left, right = 'L16', 'strong_square_scaled'
        elif name == 'L17':
            gates += [['aux_f2_minus_one', '-', 'L16', 1],
                      ['aux_reduced_coefficient', '*', 'A', 'aux_f2_minus_one']]
            left = 'aux_reduced_coefficient'
        elif name == 'polynomial':
            right = 1
        gates.append([name, operation, left, right])
    return dict(
        name='p69_unscaled_reduced_auxiliary',
        witness_domain=original['witness_domain'],
        witnesses=original['witnesses'],
        fixed_numerals=original['fixed_numerals'],
        source=gates,
        output='polynomial',
        coefficient_binding=original['coefficient_binding'],
        provenance=dict(source=str(SOURCE.relative_to(ROOT)),
                        sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                        change='Unscale the strong factor and final target; reduce auxiliary coefficient to Delta*(f^2-1).'),
        proof_boundary='Local zero equivalence to P67 on Delta != 0 is proved in ShortEquation.lean. The native-window compiler semantics are not certified here.',
    )


if __name__ == '__main__':
    result = build()
    # Bind coefficients to the original complete tuple using a path from here.
    result['coefficient_binding']['file'] = '../../../' + str(
        SOURCE.parent.parent.relative_to(ROOT)) + '/coefficients/COEFFICIENT_BINDING.json'
    DEST.write_text(json.dumps(result, indent=2) + '\n')
    print(DEST.relative_to(ROOT))
