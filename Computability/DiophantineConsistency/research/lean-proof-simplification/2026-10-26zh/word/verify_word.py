#!/usr/bin/env python3
"""Read-only checks of our candidate text and finite mathematical models.

No Lean, repository script, incoming executable, network request, or file write.
This is not a Lean compilation or a proof of an unbounded Lean theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline-tree', type=Path, default=ROOT.parent/'baseline',
    help='Read-only repository root; defaults to the extracted package baseline directory.')
args = parser.parse_args()
SRC = args.baseline_tree / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordTopBounds2011.lean'
DST = ROOT / 'candidates/CurrentWordTopBounds2011.lean'
old, new = SRC.read_text(encoding='utf-8'), DST.read_text(encoding='utf-8')

def check(condition, message):
    if not condition:
        raise RuntimeError(message)

def signatures(text):
    return {m.group(1): re.sub(r'\s+', ' ', m.group(2)).strip()
        for m in re.finditer(r'^theorem (\w+)(.*?)(?::=)', text, re.M | re.S)}

a, b = signatures(old), signatures(new)
check(hashlib.sha256(old.encode('utf-8')).hexdigest() == '7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f',
    'Baseline source differs from the pinned reviewed file')
check(set(a) <= set(b), 'Old public theorem disappeared')
check(all(a[k] == b[k] for k in a), 'Old public theorem signature changed')
check(new.count('omit [NeZero N] in') == old.count('omit [NeZero N] in'), 'Domain omission changed')
prefix = old[:old.index('theorem word_zero_high')]
suffix = old[old.index('theorem rotation_high_zero'):]
check(new.startswith(prefix) and new.endswith(suffix), 'Candidate modified text outside priced section')
check(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', new), 'Untrusted proof escape added')
check(re.findall(r'^import .+$', old, re.M) == re.findall(r'^import .+$', new, re.M), 'Imports changed')
tail_signature = '(a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (j : ZMod N) (h : ℕ) (hl : 1991 ≤ h) (hh : h < 2011) : convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j+(h : ZMod (N*2011))) = (if h = 2008 then marker j else 0) + ∑ e : Entry, if h+position e = 2009 then 2*weight e*marker j else 0'
check(b['convolution_marker_tail'] == tail_signature, 'New theorem statement differs from finite model specification')

def support(x):
    return x < 951 or 960 <= x < 986 or x == 1004

geometry = 0
for h in range(1991, 2011):
    for p in range(986):
        source = h - (1005 - p)
        check(986 <= source < 2011, 'Reflected source escaped terminal cell')
        check(support(source) == (h + p == 2009), 'Reflected support classification failed')
        geometry += 1
    for d in (18, 1004, 2020):
        residue = (h - d) % 2011
        check(support(residue) == (h == 2008 and d == 1004), 'Bare source classification failed')

cyclic_geometry = 0
for N in (1, 2, 3, 7):
    n = N * 2011
    for j in range(N):
        for h in range(1991, 2011):
            for p in range(986):
                x = (j*2011 + h - (1005-p)) % n
                check(x == j*2011 + h - 1005+p, 'Reflected term crossed cells')
                check(support(x % 2011) == (h+p == 2009), 'Cyclic reflected classification failed')
                cyclic_geometry += 1
            for d in (18, 1004, 2020):
                x = (j*2011 + h - d) % n
                check(support(x % 2011) == (h == 2008 and d == 1004), 'Cyclic bare classification failed')

# The physical permutation gives selectors0..941 once; the true control
# positions have exactly the four documented block ranges. We do not read
# or execute a generated tile table or claim to authenticate its weights.
positions = list(range(942)) + list(range(978, 986)) + list(range(960, 969)) + list(range(969, 977)) + list(range(942, 951))
check(len(positions) == len(set(positions)) == 976, 'Model entry positions not injective')
weights = {p: 1 + (37*p) % 997 for p in positions}

def kernel_value(c, k):
    n = len(c)
    return sum(c[(k-d) % n] for d in (18, 1004, 2020)) + sum(
        2*weights[p]*c[(k-(1005-p)) % n] for p in positions)

finite_sums = 0
omission_counterexample = None
for N in (1, 2, 3, 7):
    for seed in (0, 1, 2, 17):
        c = [((x*29 + seed*7 + x//2011) % 31) if support(x % 2011) else 0 for x in range(N*2011)]
        markers = [seed + 3*j for j in range(N)]
        for j, m in enumerate(markers):
            c[j*2011+1004] = m
        for j, m in enumerate(markers):
            for h in range(1991, 2011):
                actual = kernel_value(c, j*2011+h)
                reflected = sum(2*weights[p]*m for p in positions if h+p == 2009)
                predicted = (m if h == 2008 else 0) + reflected
                check(actual == predicted, 'Full finite convolution disagrees')
                if h == 2008 and m and omission_counterexample is None:
                    omission_counterexample = dict(N=N, cell=j, marker=m,
                        actual=actual, wrong_without_bare_collision=reflected)
                finite_sums += 1
check(omission_counterexample is not None, 'Failed to reject missing field2008 collision')

# A supported source at985 witnesses that1991 cannot be replaced by1990.
c = [0]*2011
c[985] = 1
threshold_actual = kernel_value(c, 1990)
check(threshold_actual == 2*weights[0] > 0, 'Sharp-threshold counterexample failed')

# The boundary also fails on the actual Start-tile construction, not only
# arbitrary supported digits: tile0 has west2, so complement253 has bit7=1.
# All terms except position0 vanish, so no other942-tile weight is needed.
core = (SRC.parent / 'WangTiles942Core.lean').read_text(encoding='utf-8')
check('def start : Tile := ⟨2, 435, 3, 1⟩' in core, 'Actual Start data changed')
check('1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)' in core,
    'Actual selector coefficient recipe changed')
start_weight = 1 + 2**10 * (1 + 2 + 2**8*435 + 2**17*3 + 2**25*1)
start = [0]*2011
start[0] = 1
for lo, width, complement in ((942,9,510),(960,9,76),(969,8,252),(978,8,253)):
    for bit in range(width):
        start[lo+bit] = (complement // 2**bit) % 2
check(start[985] == 1 and start[1004] == 0, 'Start-cell boundary bit changed')
check(all(start[(1990-(1005-p)) % 2011] == 0 for p in positions if p != 0),
    'A non-Start coefficient unexpectedly survives at1990')
check(all(start[(1990-d) % 2011] == 0 for d in (18,1004,2020)), 'Bare term survives at1990')
actual_start_counterexample = 2*start_weight

print(json.dumps(dict(status='passed',
    validation_scope='Source/static and finite models only; Lean compilation and axiom checks NOT RUN.',
    source_sha256=hashlib.sha256(old.encode()).hexdigest(),
    candidate_sha256=hashlib.sha256(new.encode()).hexdigest(),
    old_theorem_signatures_preserved=len(a), new_theorems=sorted(set(b)-set(a)),
    no_import_changes=True, all_prior_NeZero_omissions_preserved=True,
    reflected_geometry_checks=geometry, bare_geometry_checks=60,
    cyclic_reflected_checks=cyclic_geometry, full_weighted_convolution_checks=finite_sums,
    moduli_cells=[1,2,3,7], numeric_seeds=[0,1,2,17],
    sharp_threshold=dict(field=1990, source=985, position=0, actual=threshold_actual, wrong_tail_formula=0),
    actual_Start_counterexample=dict(N=1, tile=0, dummy=0, marker=0, field=1990,
        source=985, source_digit=1, selector_weight=start_weight,
        actual_convolution=actual_start_counterexample, wrong_tail_formula=0),
    omitted_bare_collision_counterexample=omission_counterexample,
    limitations=['Finite tests do not establish universal quantifiers.',
        'Model weights are arbitrary small integers, not an authenticated942-tile table.',
        'No Lean executable, incoming executable, network action, or dependency installer was invoked.']), indent=2))
