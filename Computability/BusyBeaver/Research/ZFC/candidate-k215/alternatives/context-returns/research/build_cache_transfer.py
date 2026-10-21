#!/usr/bin/env python3
"""Reconstruct and independently check the cache-return/transfer-pop sources.

The construction is exact and deterministic. The literal command executions
are explicitly finite regressions; the all-natural theorem is in
cache_transfer_proof.md. This does not certify a binary transition table.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
from math import isqrt

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
BASE = ROOT / 'machine'
spec = importlib.util.spec_from_file_location('source_language', ROOT / 'code/source_language.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    a = (isqrt(8 * n + 1) - 1) // 2
    b = n - a * (a + 1) // 2
    return a - b, b


def fields(code, tail):
    for field in reversed(code):
        tail = pair(field, tail)
    return tail


def run(graph, entry, stop=0, limit=1_000_000):
    """Run one literal source command, or stop before a named AX entry."""
    v = list(entry)
    pc = 0
    for steps in range(limit):
        if steps and pc == stop:
            return 'return', v, steps
        effect, targets = graph[pc]
        if effect[0] == 'halt':
            return 'halt', v, steps + 1
        if effect[0] == 'increment':
            v[effect[1]] += 1
            pc = targets[0]
        elif effect[0] == 'decrement':
            k = effect[1]
            branch = int(v[k] > 0)
            v[k] -= branch
            pc = targets[branch]
        else:
            pc = targets[0]
    raise RuntimeError('Fuel exhaustion; this is not counted as a successful check')


def construct():
    raw = (BASE / 'sites215.json').read_bytes()
    baseline = s.tree(json.loads(raw))
    assert hashlib.sha256(raw).hexdigest() == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    old_drop = s.subtree(baseline, '110101')
    old_nip = s.subtree(baseline, '111')
    copy_h = s.subtree(baseline, '1101011')
    clear_t = (('CD', 1), ('CC', 1))
    changed = s.replace(baseline, '11010010111', (('CD', 4), (('CI', 5), ('CC', 2))))
    changed = s.replace(changed, '11010', s.subtree(changed, '11010010'))
    shifts = {
        'direct-left': ((clear_t, copy_h), old_nip),
        'direct-right': (clear_t, (copy_h, old_nip)),
        'DNN-left': ((old_drop, old_nip), old_nip),
        'DNN-right': (old_drop, (old_nip, old_nip)),
    }
    result = []
    for tag, shift in shifts.items():
        root = s.replace(changed, '111', shift)
        for swap in (False, True):
            variant = root
            name = tag
            if swap:
                mp = s.subtree(root, '110101')
                variant = s.replace(s.replace(root, '110101', shift), '111', mp)
                name += '-swap01'
            rows = s.sites(variant)
            assert s.boundary(variant) == (0, 0, True)
            assert s.graph_arithmetic(rows)[0] == s.graph_intervals(rows)
            assert s.subtree(variant, '1101001') == s.subtree(baseline, '1101001001')
            raw = s.compact(rows)
            path = OUT / f'sites-cachetransfer-{name}.json'
            path.write_bytes(raw)
            result.append((name, rows, variant, swap, tag.startswith('DNN')))
    return result


def check_variant(name, rows, root, swap, extra_top_guard):
    graph = s.graph_arithmetic(rows)[0]
    mp_opcode, s_opcode = (0, 1) if swap else (1, 0)
    count_s = count_mp = count_ax_dispatch = longest = 0
    for t in (0, 1, 2, 7):
        for w in range(13):
            for d in (0, 1, 4):
                for h in (0, 1, 2, 5, 17):
                    for tail in (0, 3):
                        entry = [17, t, w, 0, d, h, 0, 0, 1 + fields([s_opcode], tail)]
                        status, out, steps = run(graph, entry)
                        longest = max(longest, steps)
                        if h == 1 or (extra_top_guard and t == 1):
                            assert status == 'halt', (name, entry, status, out)
                        else:
                            x, rest = unpair(w)
                            expected = [17, h, rest, 0, d, x, 0, 0, tail]
                            assert status == 'return' and out == expected, (name, entry, status, out, expected)
                        count_s += 1
    for t in range(4):
        for w in range(4):
            for d in range(3):
                for x in range(3):
                    y = d + x
                    major = 4 * pair(t, y)
                    for h in sorted({0, 1, major, max(0, major - 1), major + 1}):
                        for tail in (0, 2):
                            entry = [17, t, w, 0, d, h, 0, 0, 1 + fields([mp_opcode, x], tail)]
                            status, out, steps = run(graph, entry)
                            longest = max(longest, steps)
                            success = major == h
                            expected = [17, 0, w, 0, 0 if success else y, y if success else 0, 0, 0, tail]
                            assert status == 'return' and out == expected, (name, entry, status, out, expected)
                            count_mp += 1
    ax_entry = next(i for i, row in enumerate(rows) if row[0].startswith('1101001'))
    for c in range(5):
        for x in range(3):
            for y in range(3):
                for tail in (0, 2):
                    entry = [17, 3, 5, 0, 7, 11, 0, 0, 1 + fields([c + 2, y, x], tail)]
                    status, out, steps = run(graph, entry, stop=ax_entry)
                    longest = max(longest, steps)
                    expected = [17, 3, 5, c, 7, 11, 0, 0, fields([y, x], tail)]
                    assert status == 'return' and out == expected, (name, entry, status, out, expected)
                    count_ax_dispatch += 1
    path = OUT / f'sites-cachetransfer-{name}.json'
    return {
        'variant': name,
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        **s.metrics(root),
        'status': 'PASS',
        'literal_S_executions': count_s,
        'literal_MP_executions': count_mp,
        'literal_AX_dispatch_executions': count_ax_dispatch,
        'longest_literal_regression': longest,
        'AX_body_identical_to_baseline': True,
        'independent_CFG_resolvers_agree': True,
        'fields': {'S': [s_opcode], 'MP': [mp_opcode, 'x'], 'AX': ['c+2', 'y', 'x']},
        'S_extra_top_one_guard': extra_top_guard,
    }


if __name__ == '__main__':
    variants = construct()
    results = [check_variant(*variant) for variant in variants]
    packet = {
        'status': 'PASS',
        'scope': 'Exact source construction and finite complete-command/dispatch checks. The separate ordinary all-natural proof is cache_transfer_proof.md. No physical state-count or binary-runtime claim.',
        'variants': results,
    }
    (OUT / 'cache_transfer_source_results.json').write_text(json.dumps(packet, indent=2) + '\n')
    print(json.dumps(packet, indent=2))
