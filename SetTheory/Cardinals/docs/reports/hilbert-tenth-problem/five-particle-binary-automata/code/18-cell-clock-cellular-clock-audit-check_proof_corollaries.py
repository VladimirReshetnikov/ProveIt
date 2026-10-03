#!/usr/bin/env python3
"""Independent exact algebra and short saved-row replay for the proof review."""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from verify_pins import verify_inputs
from baseline_support import regenerated_baseline
OPT = ROOT


def require(ok, detail):
    if not ok:
        raise RuntimeError(detail)


def read(root, name):
    return json.loads((root / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficients(op, prime, multiplier):
    """Coefficients of X^2, lambda*X, X, 1 for input N=multiplier*X."""
    k = Fraction(multiplier)
    if op == '+':
        return ((prime * prime + 3) * k * k, (prime + 3) * k, 4 * k, Fraction(3))
    require(multiplier % prime == 0, 'Division/test polynomial domain')
    q = k / prime
    if op == '-':
        return (3 * k * k + q * q, 3 * k + q, 2 * (k + q), Fraction(3))
    require(op == 'P', 'Unexpected phase operation')
    return (2 * (k * k + q * q), 2 * (k + q), 2 * (k + q), Fraction(3))


def run(OLD):
    verify_inputs()
    old, new = read(OLD, 'certificates.json'), read(OPT, 'certificates.json')
    old_by_target = {x['target']: x['incoming'] for x in old['history']}
    new_by_target = {x['target']: x['incoming'] for x in new['history']}
    require(old_by_target.keys() == new_by_target.keys(), 'Pair targets changed')
    changed = [q for q in old_by_target if old_by_target[q] != new_by_target[q]]
    require(len(changed) == 4, 'Wrong number of changed pairs')
    old_bits = {name: bit for x in old['history'] for bit, name in enumerate(x['incoming'])}
    new_bits = {name: bit for x in new['history'] for bit, name in enumerate(x['incoming'])}
    startup_edges = ['entry', 'v0000d', 'v0000z', 'n0001e0', 'n0001e1', 'n0001e2', 'n0001e3']
    require([old_bits[n] for n in startup_edges] == [0, 1, 0, 1, 1, 1, 1], 'Predecessor startup bits')
    require([new_bits[n] for n in startup_edges] == [0, 1, 0, 0, 0, 0, 0], 'Optimized startup bits')
    # Appending bits maps h -> 2^k*h + the value of that k-bit string.
    suffix_old = ''.join(str(old_bits[n]) for n in startup_edges[2:])
    suffix_new = ''.join(str(new_bits[n]) for n in startup_edges[2:])
    require((len(suffix_old), int(suffix_old, 2), int(suffix_new, 2)) == (5, 15, 0), 'Startup affine suffix')

    phases = {
        'transfer': [('P', 7, 7), ('-', 7, 7), ('+', 11, 1), ('P', 11, 11)],
        'preparation': [('+', 7, 1), ('P', 7, 7)],
        'doubling': [('P', 11, 11), ('-', 11, 11), ('+', 7, 1), ('P', 7, 7), ('+', 7, 7), ('P', 7, 49)],
    }
    expected = {'transfer': [616, 76, 60, 12], 'preparation': [152, 26, 20, 6], 'doubling': [8208, 266, 208, 18]}
    for name, word in phases.items():
        total = [sum(c) for c in zip(*(coefficients(*op) for op in word))]
        require(total == expected[name], ('Phase coefficient identity', name, total))

    source = read(OPT, 'source.json')
    require(sha(OPT / 'source.json') == 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3', 'Source pin')
    groups = defaultdict(list)
    for row in source['branches']:
        groups[row['source']].append(row)
    lam = 36684691
    replays = []
    for name in ('empty-prologue-literal-trace.json', 'empty-first-tm-literal-trace.json', 'empty-through-first-tm-literal-trace.json'):
        saved = read(OPT, name)
        trace = saved['trace']
        q, v, total = trace[0]['control'], trace[0]['counters'].copy(), 0
        for index, entry in enumerate(trace):
            require(entry['step'] == index and entry['control'] == q and entry['counters'] == v, 'Saved trace state')
            eligible = []
            for row in groups[q]:
                g = row['guard']
                if g['op'] == 'true' or (v[g['counter']] == 0 if g['op'] == 'eq' else v[g['counter']] > 0):
                    eligible.append(row)
            require(len(eligible) == 1, 'Replay determinism')
            row = eligible[0]
            require(row['name'] == entry['branch'], 'Saved branch')
            selected = 0 if row['side'] == -1 else 1
            d = row['delta']
            cost = 1 if d == 0 else lam + abs((v[selected] + d) ** 2 - v[selected] ** 2)
            require(cost == entry['predicted_CA_microedges'], 'Saved row clock')
            total += cost
            v[selected] += d
            q = row['target']
        require((q, v, len(trace), total) == (saved['control'], saved['counters'], saved['steps'], saved['predicted_CA_microedges']),
                'Saved final state/counts')
        replays.append({'file': name, 'sha256': sha(OPT / name), 'literal_rows': len(trace), 'derived_CA_clock': total})
    receipt = {
        'status': 'PASS', 'mode_policy': 'Executed separately under normal and -O by run_checks.py',
        'changed_pair_targets': changed,
        'old_startup_bits': {n: old_bits[n] for n in startup_edges},
        'new_startup_bits': {n: new_bits[n] for n in startup_edges},
        'startup_suffix_affine_constants': {'scale': 32, 'old_addend': 15, 'new_addend': 0},
        'phase_polynomial_coefficients_X2_lambdaX_X_constant': expected,
        'saved_literal_trace_replays': replays,
        'reviewed_proof_sha256': sha(HERE.parent / 'CA_CLOCK_DOMINATION.md'),
        'checker_sha256': sha(Path(__file__)),
        'scope': 'Exact rational coefficient identities and literal source-row replay; no CA execution or gate allocation',
    }
    output = HERE / 'corollaries-receipt.json'
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


def main():
    with regenerated_baseline() as baseline:
        run(baseline)


if __name__ == '__main__':
    main()
