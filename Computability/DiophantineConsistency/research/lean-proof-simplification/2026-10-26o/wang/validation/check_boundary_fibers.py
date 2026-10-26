#!/usr/bin/env python3
"""Finite sanity audit of proposed fibers using the pinned Lean source data.

This does NOT parse or elaborate the Lean proof, authenticate the decimal
machine, or replace kernel checking. It detects wrong colors, lost families,
and accidentally deleted exceptional witnesses in the proposal.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', type=Path, default=ROOT.parent / 'baseline',
                    help='Repository root (default: packaged sibling baseline directory)')
parser.add_argument('--output', type=Path, help='Explicitly write the JSON receipt; default is stdout only')
args = parser.parse_args()
SRC = args.baseline / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'

def require(condition, message):
    if not condition:
        raise ValueError(message)

data = (SRC / 'WangTiles942Data.lean').read_text()
core = (SRC / 'WangTiles942Core.lean').read_text()
require(hashlib.sha256(data.encode()).hexdigest() ==
        'ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125',
        'Data baseline differs from the pinned source.')
require(hashlib.sha256(core.encode()).hexdigest() ==
        '7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85',
        'Core baseline differs from the pinned source.')
action_text = data.split('def actionCache : Array Action := #[', 1)[1].split(' ]', 1)[0]
actions = [(w == 'true', d == 'true', int(q)) for w,d,q in
           re.findall(r'\((true|false), (true|false), (\d+)\)', action_text)]
require(len(actions) == 430, 'Expected 430 actions.')

def bool_lists(name, array=False):
    body = data.split('def ' + name + ' ', 1)[1].split('\n\n', 1)[0]
    match = re.search(r'if d then #?\[([^]]*)\] else #?\[([^]]*)\]', body)
    require(match is not None, 'Malformed boolean list: ' + name)
    return {True: [int(x) for x in match[1].split(',')],
            False: [int(x) for x in match[2].split(',')]}

targets = bool_lists('targetList')
rails = bool_lists('railCache', array=True)
for d in [False, True]:
    require(targets[d] == sorted({q for _, dd, q in actions if dd == d}), 'Target list/action mismatch.')
    require(len(rails[d]) == 216, 'Expected 216 rail cache entries.')
    require(rails[d] == [205 - 199 * int(d) + sum(p < q for p in targets[d])
                        for q in range(216)], 'Rail cache/rank mismatch.')
require(actions[125] == (True, True, 215), 'Actual halt action changed.')
require(215 in targets[True] and 215 not in targets[False], 'Halt direction target mismatch.')

# Formula spellings are deliberately checked so source changes require review.
require('⟨2, 435, 3, 1⟩' in core, 'Start spelling changed.')
require('(928,⟨3,436,4,4⟩)' in core, 'Initializer spelling changed.')
require('(933+3*a+b,⟨a^2,437,b,437⟩)' in core, 'Seam formula changed.')
start = (2,435,3,1)
left, head, right = (2,434,2,0), (3,436,4,4), (4,436,4,0)
resets = {(1,438,1,p) for p in [434,435,436]}
seams = {(a*a,437,b,437) for a in range(3) for b in range(3)}
finishes = {(0,432*a+b,0,438) for a in range(2) for b in range(2)}
rows = {0: start}
for j, (w,d,q) in enumerate(actions):
    rows[j+1] = ((1-int(d))*rails[False][q], 2*(j//2)+j%2+2,
                 int(d)*rails[True][q], int(w))
for a in range(2):
    for b in range(2):
        rows[433-2*a+b] = (0,432*a+b,0,432*a+b)
for d in [False, True]:
    for q in targets[d]:
        for b in range(2):
            r = rails[d][q]
            rows[423+2*r+b] = (int(d)*r,b,(1-int(d))*r,2*q+b+2)
for a in range(2):
    for b in range(2):
        rows[923+2*a+b] = (0,432*a+b,0,438)
rows.update({927:left, 928:head, 929:right})
for p in [434,435,436]:
    rows[496+p] = (1,438,1,p)
for a in range(3):
    for b in range(3):
        rows[933+3*a+b] = (a*a,437,b,437)
require(sorted(rows) == list(range(942)), 'Indexed rows do not cover 0..941.')
require(len(set(rows.values())) == 942, 'Expected 942 distinct rows.')
require(rows[928] == (3,436,4,4), 'Wrong actual initializer.')
require((3,436,4,188) not in rows.values(), 'Obsolete initializer was admitted.')
require((0,0,0,0) in rows.values(), 'Ordinary empty tile was lost.')  # Empty ordinary tile is not removed.
require((4,437,2,437) in rows.values(), 'Genuine seam exception was lost.')
require((2,437,0,437) not in rows.values(), 'Nonsquare seam edge was admitted.')  # No nonsquare seam west edge.

def north_fiber(t,c):
    return ((c == 435 and t == start) or
            (c == 434 and t == left) or
            (c == 436 and t in [head,right]) or
            (c == 438 and t in resets) or
            (c == 437 and t in seams))

def south_fiber(t,c):
    return ((c == 438 and t in finishes) or
            (c in [434,435,436] and t == (1,438,1,c)) or
            (c == 437 and t in seams))

checks = 0
for t in rows.values():
    for c in range(434,513):
        require((t[1] == c) == north_fiber(t,c), f'North fiber mismatch: {t}, {c}')
        require((t[3] == c) == south_fiber(t,c), f'South fiber mismatch: {t}, {c}')
        checks += 2
# Every vertical color is ≤438; formulas have no high-color true branch beyond 438.
require(max(t[1] for t in rows.values()) == 438, 'Wrong maximum north color.')
require(max(t[3] for t in rows.values()) == 438, 'Wrong maximum south color.')
# The lower guard cannot be dropped: an allowed blank has north/south 0,
# while neither proposed high-color RHS has any c=0 branch.
blank = (0,0,0,0)
require(blank[1] == 0 and not north_fiber(blank,0), 'Missing north guard counterexample.')
require(blank[3] == 0 and not south_fiber(blank,0), 'Missing south guard counterexample.')
result = {
    'status': 'PASS (Python finite-family sanity audit only)',
    'baseline_commit': 'b310142330df89e48413c8fce62e7de223e1c7d5',
    'data_sha256': hashlib.sha256(data.encode()).hexdigest(),
    'core_sha256': hashlib.sha256(core.encode()).hexdigest(),
    'parsed_actions': len(actions),
    'target_counts_false_true': [len(targets[False]),len(targets[True])],
    'reconstructed_indexed_rows': len(rows),
    'checked_color_range_inclusive': [434,512],
    'fiber_equivalence_checks': checks,
    'north_fiber_cardinalities': {str(c):sum(t[1]==c for t in rows.values()) for c in range(434,439)},
    'south_fiber_cardinalities': {str(c):sum(t[3]==c for t in rows.values()) for c in range(434,439)},
    'guard_negative_test': 'blank tile at c=0 refutes both unguarded statements',
    'semantic_regressions': ['initializer south=4, not188', 'halt target215 retained',
                             'blank ordinary tile retained', 'all9 square-west seam tuples retained'],
    'lean_kernel_validation': 'NOT RUN',
    'limitation': 'Python transcription of pinned family formulas, not a proof of Lean elaboration or decimal decoding.'}
rendered = json.dumps(result, indent=2) + '\n'
if args.output is not None:
    args.output.write_text(rendered)
print(rendered, end='')
