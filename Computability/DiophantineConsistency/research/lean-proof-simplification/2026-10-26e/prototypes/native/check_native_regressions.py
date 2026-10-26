#!/usr/bin/env python3
"""Finite sanity checks for proposal boundaries. NOT a Lean proof or build.

Results go to stdout only; replay never modifies sealed regression_results.json.
Redirect stdout explicitly if a separate fresh run record is desired.
"""
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', type=Path,
                    help='Original-source root containing Computability/ (default: baseline/ or upstream/).')
args = parser.parse_args()
baseline = args.baseline if args.baseline is not None else (
    ROOT / 'baseline' if (ROOT / 'baseline').is_dir() else ROOT / 'upstream')
SRC = baseline / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'


def require(condition, message):
    # Unlike assert, this remains active under python -O.
    if not condition:
        raise RuntimeError(message)

results = {}
text = (SRC / 'WangTiles942Data.lean').read_text()
for family, length, pattern in [
    ('action', 430, r'private theorem action_chunk_(\d+) : ∀ j : Fin (\d+)'),
    ('rail', 216, r'private theorem rail_chunk_(\d+) : ∀ \(d : Bool\) \(q : Fin (\d+)\)'),
]:
    blocks = [(int(a), int(n)) for a, n in re.findall(pattern, text)]
    covered = [j for a, n in blocks for j in range(a, a+n)]
    require(covered == list(range(length)), f'{family}: incomplete or overlapping source blocks: {blocks}')
    results[family + '_blocks'] = {'count': len(blocks), 'coverage': length,
                                  'last_start': blocks[-1][0], 'last_length': blocks[-1][1]}

cases = 0
for radix in range(1, 21):
    for digit in range(0, 41):
        for outgoing in range(0, 11):
            total = digit + radix*outgoing
            if total < radix:
                require(outgoing == 0 and digit == total,
                        f'reset failed: radix={radix}, digit={digit}, outgoing={outgoing}')
            for modulus in range(1, 21):
                if radix % modulus == 0:
                    require(total % modulus == digit % modulus,
                            f'residue failed: radix={radix}, digit={digit}, outgoing={outgoing}, modulus={modulus}')
            cases += 1
results['equation_lemma_finite_sanity_cases'] = cases

# Preserve the repository's counterexamples to tempting invalid shortcuts.
phase10_raw = 2*512 + 2**10 + 2048*(2**34-1)
require(phase10_raw & (2**45-4) == 0 and 512 > 1, 'phase10 count512 counterexample failed')
require((2*511+1) % 512 == 511, 'offset19 511 self-loop counterexample failed')
results['counterexamples'] = {
    'full_clause_mask_alone_allows_phase10_count512': True,
    'offset19_permits_511_self_loop': True,
}

radix = 2**47
mass = 7659829036801887
carry_margin = 58*radix - (mass + 2**46 + 57)
early_margin = radix - (137820284543942 + 2**10 + 60)
require(carry_margin > 0 and early_margin > 0, 'strict numeric carry/reset budget failed')
results['numeric_margins'] = {'carry57_strict_margin': carry_margin,
                              'early_padding_strict_margin': early_margin}
results['status'] = 'PASS: finite Python checks only; Lean prototypes uncompiled'
print(json.dumps(results, indent=2))
