#!/usr/bin/env python3
"""Certify that every control state is distinct under unrestricted read inputs.

This excludes ordinary deterministic output-preserving control quotients only.
Read words used here need not occur on a real tape. This is NOT a lower bound
on blank-input Turing machines, or on simulations using tape invariants.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

HALT = 254

def read_table(path):
    raw = Path(path).read_bytes()
    table = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in table
        table[key] = int(w), d, int(n)
    states = sorted({q for q, b in table})
    assert len(states) == 215 and len(table) == 430 and HALT not in states
    assert all(n in states or n == HALT for w, d, n in table.values())
    return raw, table, states

def pair(a, b):
    return (a, b) if a < b else (b, a)

def distinguish(table, a, b, word):
    for bit in word:
        if (a == HALT) != (b == HALT):
            return True
        if a == HALT:
            return False
        x, y = table[a, bit], table[b, bit]
        if x[:2] != y[:2]:
            return True
        a, b = x[2], y[2]
    return (a == HALT) != (b == HALT)

def certify(path, output):
    raw, table, states = read_table(path)
    witness = {pair(q, HALT): () for q in states}
    pairs = [(a, b) for a in states for b in states if a < b]
    rounds = []
    while any(p not in witness for p in pairs):
        old = dict(witness)
        for a, b in pairs:
            if (a, b) in old:
                continue
            options = []
            for bit in (0, 1):
                x, y = table[a, bit], table[b, bit]
                if x[:2] != y[:2]:
                    options.append((bit,))
                elif x[2] != y[2] and pair(x[2], y[2]) in old:
                    options.append((bit,) + old[pair(x[2], y[2])])
            if options:
                witness[a, b] = min(options, key=lambda w: (len(w), w))
        rounds.append(sum(p in witness for p in pairs))
        assert len(witness) > len(old), 'nontrivial control quotient exists'
    # Replay every certificate with a separate trace evaluator.
    records = []
    for (a, b) in pairs:
        word = witness[a, b]
        assert distinguish(table, a, b, word)
        records.append([a, b, ''.join(map(str, word))])
    summary = {
        'machine_sha256': hashlib.sha256(raw).hexdigest(),
        'working_states': len(states), 'rows': len(table),
        'working_pairs_certified': len(records),
        'maximum_distinguishing_word_length': max(map(lambda r: len(r[2]), records)),
        'pairs_distinguished_after_each_round': rounds,
        'conclusion': 'Every output-preserving read-input control congruence is equality.',
        'scope': 'No claim about state minimality on real tapes or blank input.'
    }
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    with gzip.GzipFile(str(output / 'witnesses.json.gz'), 'wb', mtime=0) as f:
        f.write(json.dumps(records, separators=(',', ':')).encode())
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('machine')
    ap.add_argument('output')
    args = ap.parse_args()
    certify(args.machine, args.output)
