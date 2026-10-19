#!/usr/bin/env python3
"""Independently audit and compile a finest-closed-atom routed grammar.

The source dictionary and atom meanings are rederived from the immutable
245-state package, not from the searcher's canonical-map.json.  Search data
are certificates only.  Complete runtime checks use the inherited separately
audited symbolic executor and its actual-table register induction checker.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from functools import cache
import hashlib
import json
from pathlib import Path
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def put(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def load_model(reference):
    source = json.loads((reference / 'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((reference / 'inputs/semantic-symbols.json').read_text())
    ast = source['ast_dag']

    @cache
    def bounds(i):
        row = ast[i]
        if row[0] == 'L':
            op, *arg = row[1]
            return ((1, 0) if op == 'dec' else (arg[0], 0) if op == 'brk'
                    else (0, arg[0]) if op == 'cont' else (0, 0))
        a, b = bounds(row[1]), bounds(row[2])
        return max(a[0]-1, b[0], 0), max(a[1], b[1]-1, 0)

    @cache
    def finest(i):
        row = ast[i]
        if row[0] == 'N' and bounds(row[1]) == bounds(row[2]) == (0, 0):
            return finest(row[1]) + finest(row[2])
        return (i,)

    assert all(bounds(atom['ast']) == (0, 0) for atom in source['atoms'].values()), 'Every dictionary atom must be closed.'
    fine = {c: finest(source['atoms'][name]['ast']) for c, name in symbols.items()}
    all_ids = sorted({i for word in fine.values() for i in word})
    alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
    assert len(all_ids) <= len(alphabet)
    code = {i: alphabet[j] for j, i in enumerate(all_ids)}
    encoded = {c: ''.join(code[i] for i in word) for c, word in fine.items()}
    assert len(set(encoded.values())) == len(encoded) == 44

    def encode(word):
        return ''.join(encoded[c] for c in word)

    decode_symbol = {name: c for c, name in symbols.items()}
    names = {int(q): encode(''.join(decode_symbol[x] for x in word))
             for q, word in source['flattened_semantic_words'].items()}
    atoms = {encoded[c]: source['atoms'][name] for c, name in symbols.items()}
    lines = (reference / 'inputs/semantic.txt').read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    assert (n, nr, na) == (127, 24, 44)
    masks = {encoded[c]: int(mask) for c, mask in map(str.split, lines[n+nr+1:])}
    for q, i in source['sequence_ast_roots'].items():
        assert names[int(q)] == ''.join(code[x] for x in finest(int(i)))
    return source, ast, atoms, masks, names, encode, finest, code


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--scanner-zero-limit', type=int, choices=(5, 6), default=6)
    ap.add_argument('--boot-limit', type=int, default=2000000)
    ap.add_argument('--padding', type=int, default=64)
    ap.add_argument('--require-bootstrap-lock', action='store_true')
    ap.add_argument('--audit-only', action='store_true')
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError('Assertions are required.')
    began = time.monotonic()
    reference = args.reference.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source, ast, atoms, masks, names, encode, finest, code = load_model(reference)
    data = json.loads(args.candidate.read_text())
    assert not data.get('source_replacements'), 'Source-changing candidates require a separate AX transfer certificate.'
    rules = {w: (a, b) for w, a, b in data['rules']}
    assert len(rules) == len(data['rules']) == data['rules_count']
    assert not (set(rules) & set(atoms)), 'A semantic key has two implementations.'
    for word, children in rules.items():
        assert word == ''.join(children) and all(children)
        for bit, child in enumerate(children):
            assert child in rules or child in atoms
            if child in atoms:
                assert masks[child] & (1 << bit), (word, bit, 'illegal terminal orientation')

    routes = {(r['source'], r['read']): r['word'] for r in data['routes']}
    assert len(routes) == len(data['routes'])
    groups = defaultdict(list)
    sym = json.loads((reference / 'inputs/semantic-symbols.json').read_text())
    inv = {v: k for k, v in sym.items()}
    for c in source['left_entry_projection_constraints']:
        reason = c['reason']
        prefix = c['prefix']
        if reason.get('via') == 177:
            prefix = str(reason['previous']) + prefix
        groups[reason['source'], reason['read']].append(
            (prefix, encode(''.join(inv[x] for x in c['word']))))
    assert set(routes) == set(groups)

    def project(word, prefix):
        for bit in prefix:
            assert word in rules, ('route enters a physical atom too soon', word, prefix)
            word = rules[word][int(bit)]
        return word

    projections = []
    for key, obligations in groups.items():
        assert len(obligations) == 2 and routes[key] in rules
        for prefix, endpoint in obligations:
            assert project(routes[key], prefix) == endpoint, (key, prefix)
            projections.append(dict(source=key[0], read=key[1], prefix=prefix, endpoint=endpoint))

    sys.path.insert(0, str(reference / 'code'))
    import build_routing_machine as inherited
    rebuild = inherited.rebuild
    old, start = rebuild.read_table(reference / 'reference/context246/machine/zfc_prefix246_old.tm')
    assert start == 95 and len(old) == 492
    sequences = set(source['sequence_states'])
    erased = {177, 74} | ({58} if args.scanner_zero_limit == 5 else set())
    for q in sequences:
        assert old[q, 0] == (0, 'R', source['rules'][str(q)][0])
        assert old[q, 1] == (1, 'R', source['rules'][str(q)][1])
        assert sorted([p, b] for (p, b), row in old.items() if row[2] == q) == sorted(source['incoming'][str(q)])
    for (q, bit), row in old.items():
        if q not in sequences | erased and (q, bit) not in routes:
            if args.scanner_zero_limit == 6 and (q, bit) == (58, 0):
                continue
            if args.scanner_zero_limit == 5 and (q, bit) == (41, 0):
                continue
            assert row[2] not in erased
            if row[2] in sequences:
                assert names[row[2]] in rules, ('missing externally entered word', row[2])
    assert names[96] in rules

    boot_equations = (reference / 'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
    assert int(boot_equations[0]) == 54
    lock_failures = []
    for raw in boot_equations[1:]:
        word, bit, endpoint = raw.split()
        word, endpoint = encode(word), encode(endpoint)
        if word not in rules or rules[word][int(bit)] != endpoint:
            lock_failures.append(raw)
    if args.require_bootstrap_lock:
        assert not lock_failures

    alloc = {names[q]: q for q in sequences if names[q] in rules}
    assert len(alloc) == len(set(alloc.values()))
    available = sorted((sequences | erased) - set(alloc.values()))
    fresh = 256
    while len(available) < len(rules)-len(alloc):
        available.append(fresh)
        fresh += 1
    for word in sorted(set(rules)-set(alloc)):
        alloc[word] = available.pop(0)
    assert alloc[names[96]] == 96

    def destination(word):
        return atoms[word]['state'] if word in atoms else alloc[word]

    table = {key: row for key, row in old.items() if key[0] not in sequences | erased}
    for key, (w, d, target) in list(table.items()):
        if args.scanner_zero_limit == 6 and key == (58, 0):
            table[key] = (0, 'L', 84)
        elif args.scanner_zero_limit == 5 and key == (41, 0):
            table[key] = (0, 'L', 84)
        elif key in routes:
            table[key] = (w, d, alloc[routes[key]])
        elif target in sequences:
            table[key] = (w, d, alloc[names[target]])
    for word, (left, right) in rules.items():
        table[alloc[word], 0] = (0, 'R', destination(left))
        table[alloc[word], 1] = (1, 'R', destination(right))
    states = {q for q, bit in table}
    assert len(table) == 2*len(states)
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in table.values()}-states == {254}
    assert len(states) == len(rules) + (117 if args.scanner_zero_limit == 6 else 116)
    order = [95] + sorted(states-{95})
    mapping = {q: i for i, q in enumerate(order)} | {254: len(states)}
    canonical = {(mapping[q], b): (w, d, mapping[t]) for (q, b), (w, d, t) in table.items()}
    (out / 'machine_old.tm').write_text(rebuild.encode(table, 95))
    (out / 'machine.tm').write_text(rebuild.encode(canonical, 0))
    put(out / 'allocation.json', alloc)
    put(out / 'renumbering.json', dict(old_to_canonical=mapping, canonical_to_old=order))

    by_ast = {int(i): names[int(q)] for q, i in source['sequence_ast_roots'].items()}
    visiting = set()

    @cache
    def original(i):
        row = ast[i]
        return ('L', tuple(row[1])) if row[0] == 'L' else ('N', original(row[1]), original(row[2]))

    @cache
    def changed(i):
        if i in by_ast and by_ast[i] in rules:
            return expand(by_ast[i])
        row = ast[i]
        return ('L', tuple(row[1])) if row[0] == 'L' else ('N', changed(row[1]), changed(row[2]))

    @cache
    def expand(word):
        assert word not in visiting, ('cyclic physical-atom implementation', word)
        visiting.add(word)
        if word in atoms:
            result = changed(atoms[word]['ast'])
        else:
            a, b = rules[word]
            result = ('N', expand(a), expand(b))
        visiting.remove(word)
        return result

    before, after = original(source['original_ast']), changed(source['original_ast'])
    codes = dict(inc='CI', dec='CD', brk='CB', cont='CC', halt='CH')

    def sites(tree, physical=False):
        result = []
        for path, edge in inherited.paths(tree):
            op = codes[edge[0]]
            arg = edge[1] if len(edge) > 1 else None
            if physical and op in ('CI', 'CD'):
                arg = rebuild.PHYSICAL[arg]
            result.append([path, op, arg])
        return result

    _, pinned = inherited.review.parse_source(reference / 'reference/context246/sources/Prog254.v')
    assert sites(before, True) == pinned
    logical, physical = sites(after), sites(after, True)
    assert [(op, arg) for path, op, arg in logical] == [(op, arg) for path, op, arg in sites(before)]
    assert len(logical) == len(physical) == 6460
    maxdepth = max(len(p) for p, op, r in logical)
    maxzero = max(max(map(len, p.split('1'))) for p, op, r in logical)
    assert args.padding >= maxdepth
    put(out / 'sites_logical.json', logical)
    put(out / 'sites_physical.json', physical)
    entries = inherited.rmpath.certificate(before, after)
    bisim = inherited.check_bisimulation(before, after, entries)
    bits = lambda xs: ''.join('1' if b else '0' for b in xs)
    put(out / 'register_bisimulation.json', dict(start_pair=0, entries=[
        [bits(a), bits(b), nz, z] for a, b, nz, z in entries]))
    result = dict(status='PASS_SOURCE_AND_ROUTING_ONLY', working_states=len(states),
                  grammar_rules=len(rules), framework_states=len(states)-len(rules),
                  maximum_depth=maxdepth, maximum_zero_run=maxzero,
                  scanner_zero_limit=args.scanner_zero_limit, padding=args.padding,
                  exact_ordered_instruction_leaves=len(logical), route_projections=len(projections),
                  bootstrap_lock_equations_passed=54-len(lock_failures),
                  bootstrap_lock_failed_rows=lock_failures, source_bisimulation=bisim,
                  machine_sha256=sha(out/'machine.tm'), old_machine_sha256=sha(out/'machine_old.tm'),
                  candidate_sha256=sha(args.candidate))
    put(out / 'semantic-audit.json', result)
    print(json.dumps(result, indent=2), flush=True)
    if not args.audit_only:
        # The affine executor's accelerated register operations are admitted
        # only after their induction templates have been checked on THIS table.
        import audit_existing_machine
        macro_result = audit_existing_machine.macro_audit(table)
        put(out / 'macro-inductions.json', macro_result)
        result['actual_table_macro_inductions'] = dict(
            status=macro_result['status'], scope=macro_result['scope'])
        affine = inherited.parametric_prefix_affine
        affine.PADDING = args.padding
        result['affine_oracle_gate_checks'] = inherited.review.check_oracle(affine)
        current = {}
        native = affine.run
        def counted(*a, **kw):
            current.update(pc=a[1], branch=a[2])
            return native(*a, **kw)
        affine.run = counted
        try:
            result['affine_all_cases'] = dict(status='PASS', **inherited.check_parametric_sites(
                affine, {(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in table.items()},
                physical, args.padding))
        except Exception as exc:
            result['affine_all_cases'] = dict(status='FAIL', first_bad_case=current, error=repr(exc))
        result['blank_boot'] = inherited.sparse_boot(table, args.boot_limit, minimum_gap=args.padding)
        put(out / 'blank_boot.json', result['blank_boot'])
        if result['affine_all_cases']['status'] == 'PASS' and result['blank_boot']['status'] == 'PASS':
            result['status'] = 'PASS_SOURCE_AFFINE_AND_BOOT'
        else:
            result['status'] = 'NOT_A_VERIFIED_COMPLETE_MACHINE'
        result['seconds'] = time.monotonic()-began
        put(out / 'semantic-audit.json', result)
        print(json.dumps({k: v for k, v in result.items() if k != 'blank_boot'}, indent=2), flush=True)
        print('BOOT', result['blank_boot']['status'], result['blank_boot'].get('blank_steps'), flush=True)
        if result['status'] == 'NOT_A_VERIFIED_COMPLETE_MACHINE':
            return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
