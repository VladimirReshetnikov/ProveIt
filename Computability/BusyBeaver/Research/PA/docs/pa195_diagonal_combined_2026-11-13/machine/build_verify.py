#!/usr/bin/env python3
"""Reconstruct PA195DC and check its complete finite certificates.

Python 3, standard library only. Default: verify delivered tables and full
symbolic source contracts. --export also regenerates derived certificates.
The arithmetic-box lemmas in baseline195/vendor/reference/M6/Runtime.lean
are inherited assumptions of the symbolic checker, not replaced by sampling.
This is not a new end-to-end Lean or Rocq proof of the consistency theorem.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE / 'baseline195'
spec = importlib.util.spec_from_file_location('baseline_verifier', BASE / 'build_verify.py')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
c = b.c
need = b.need
START, HALT = 74, 254
SHA256 = 'e5cc1b2cb374fa4342070e95d8bdfd60c1bb845e7a52d44857bdee937bba7938'
# Explicit physical edits in inherited native coordinates.
EDITS = {
    (164, 1): (1, True, 130),
    (38, 0): (0, True, 11),
    (38, 1): (1, True, 122),
    (214, 0): (0, True, 312),
    (214, 1): (1, True, 20),
    (312, 0): (0, True, 188),
}


def dump(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def bind_source(old_sites, old, sites, new):
    """Exact independent CFG check and arithmetic-tail theorem binding."""
    need(old == b.interval_cfg(old_sites), 'parent independent CFG')
    need(new == b.interval_cfg(sites), 'new independent CFG')
    n = len(new)
    need(n == 3676 and len(old) == n + 24, 'source lengths')
    E, F, S = n - 15, n - 12, n - 11
    oldF, oldS = len(old) - 13, len(old) - 12
    relocate = {oldF: F, oldS: S}
    changed = []
    for i in range(E):
        oi, ni = old[i], new[i]
        nargs = 1 if oi[0] == 'jump' else 2
        if oi[0] == 'halt':
            need(oi == ni, 'halt prefix'); continue
        expected = oi[:nargs] + tuple(relocate.get(t, t) for t in oi[nargs:])
        need(expected == ni, 'source prefix mismatch at ' + str(i))
        if oi != ni:
            changed.append([i, list(oi), list(ni)])
    expected = [
        ('dec', 4, F, E + 1), ('inc', 5, E + 2), ('jump', E), ('jump', 25),
        ('dec', 1, S + 2, S + 1), ('jump', S),
        ('dec', 5, S + 6, S + 3), ('inc', 1, S + 4), ('inc', 6, S + 5),
        ('jump', S + 2), ('dec', 6, S + 9, S + 7), ('inc', 5, S + 8),
        ('jump', S + 6), ('inc', 6, S + 10), ('jump', 0),
    ]
    need(new[E:] == expected, 'exact new tail')
    need([x[0] for x in changed] == [48, n - 96, n - 16], 'relocated prefix rows')
    return dict(old_sites=len(old), new_sites=n, prefix_length=E,
                mp_success_entry=E, fetch_return=F, shift_entry=S,
                old_fetch_return=oldF, old_shift_entry=oldS,
                relocated_rows=changed, exact_tail=expected,
                independent_cfg_resolvers=2, seed_site=25)


def startup(rows, path):
    """Compare every nonzero tape cell, the head, and entry control."""
    head0 = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {head0 - 1, head0 + 48}
    expected |= {head0 + i for i, bit in enumerate(path) if bit}
    pos = head0 + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    q, head, tape = START, 0, set()
    for step in range(1, 100001):
        w, d, q = rows[q, int(head in tape)]
        (tape.add if w else tape.discard)(head)
        head += 1 if d else -1
        if (q, head, tape) == (84, head0, expected):
            need(step == 57922, 'unexpected startup length')
            return dict(literal_steps=step, native_state=q, absolute_head=head,
                        physical_register_file=physical, header_gap=48,
                        seed_path=list(path), complete_one_positions=sorted(tape),
                        outside_tape_all_zero=True)
        need(q != HALT, 'premature blank halt')
    raise ValueError('startup does not reach the exact clean tape')


def dense(rows):
    order, ix = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            n = rows[q, bit][2]
            if n != HALT and n not in ix:
                ix[n] = len(order); order.append(n)
    need(len(order) == 195 and len(rows) == 390, 'working state census')
    need(set(order) == {q for q, bit in rows}, 'unreachable advertised state')
    ix[HALT] = 195
    out = {(ix[q], bit): (w, d, ix[n])
           for (q, bit), (w, d, n) in rows.items()}
    need(set(out) == {(q, bit) for q in range(195) for bit in (0, 1)}, 'binary domain')
    need(all(0 <= n <= 195 for w, d, n in out.values()), 'target domain')
    return out, order + [HALT]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export', action='store_true')
    args = parser.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run without Python -O')
    for name, digest in json.loads((BASE / 'vendor_hashes.json').read_text()).items():
        need(hashlib.sha256((BASE / name).read_bytes()).hexdigest() == digest,
             'inherited vendor changed: ' + name)
    need((HERE / 'grammar.json').read_bytes() == (BASE / 'grammar.json').read_bytes(),
         'AX grammar changed')
    need((HERE / 'folds.json').read_bytes() == (BASE / 'folds.json').read_bytes(),
         'folds changed')
    need(hashlib.sha256((BASE / 'pa195.tm').read_bytes()).hexdigest() == b.EXPECTED_SHA,
         'parent literal hash')
    tree = c.read_grammar(HERE / 'grammar.json')
    folds = json.loads((HERE / 'folds.json').read_text())
    old_raw, old_index, old_shape = c.build(tree)
    old_folded, old_aliases = b.quotient(old_raw, folds)
    need(old_folded == b.table(BASE / 'pa195.native.tm'), 'parent native reconstruction')
    old_labels = json.loads((BASE / 'labels.json').read_text())
    old_dense = b.table(BASE / 'pa195.tm')
    need({(old_labels[q], bit): (w, d, old_labels[n])
          for (q, bit), (w, d, n) in old_dense.items()} == old_folded,
         'parent dense conjugacy')
    old_cert = b.quotient_certificate(old_raw, old_folded, folds, old_aliases)
    old_sites, old_cfg, old_contracts = c.source(tree)
    parent_binding = b.source_binding(tree, old_sites, old_cfg)
    emission = b.emitter(tree)
    old_startup = b.startup(old_dense, old_labels)
    parent_runtime = {}
    for name, rows in [('raw', old_raw), ('folded', old_folded)]:
        parent_runtime[name] = c.validate(rows, old_contracts)
        need(parent_runtime[name]['ok'], 'parent runtime ' + name)

    old_machine, old_nodes = c.machine, c.raw_nodes
    def changed_machine():
        rows, lab = old_machine()
        rows.update(EDITS)
        return rows, lab
    def changed_nodes():
        nodes = old_nodes()
        nodes['node163'] = ('node6', 'node147')
        nodes['node170'] = (('node36', ('node167', 'node145')), 'node57')
        return nodes
    c.machine, c.raw_nodes = changed_machine, changed_nodes
    raw, index, shapes = c.build(tree)
    need(len(raw) == 404 and len(shapes) == 68, 'raw census')
    need(set(raw) == set(old_raw), 'raw domain changed')
    need({key: value for key, value in raw.items() if value != old_raw[key]} == EDITS,
         'unexpected physical edits')
    folded, aliases = b.quotient(raw, folds)
    certificate = b.quotient_certificate(raw, folded, folds, aliases)
    sites, cfg, contracts = c.source(tree)
    source_binding = bind_source(old_sites, old_cfg, sites, cfg)
    need(b.word(tree) == b.word(c.read_grammar(BASE / 'grammar.json')),
         'complete emitter word differs')
    original_machine, _ = old_machine()
    need(all(folded[q, bit] == original_machine[q, bit]
             for q in c.BOXSTATES for bit in (0, 1)), 'arithmetic box rows changed')
    runtime = {}
    for name, rows in [('raw', raw), ('folded', folded)]:
        runtime[name] = c.validate(rows, contracts)
        need(runtime[name]['ok'] and runtime[name]['contracts'] == 4784,
             'new symbolic runtime ' + name)
    start = startup(folded, sites[25][0])
    dd, lab = dense(folded)
    need(b.table_bytes(dd) == (HERE / 'machine.tm').read_bytes(), 'dense table differs')
    need(b.table_bytes(folded) == (HERE / 'machine.native.tm').read_bytes(), 'native table differs')
    need(json.loads((HERE / 'labels.json').read_text()) == lab, 'state labels differ')
    need(hashlib.sha256(b.table_bytes(dd)).hexdigest() == SHA256, 'new literal hash')
    result = dict(
        name='PA195DC', working_states=195, binary_rows=390,
        dense_start=0, dense_halt=195, native_start=START, native_halt=HALT,
        graph_reachable_working_states=195, raw_working_states=202,
        fixed_core_states=134, AX_reader_states=68, simultaneous_folds=7,
        literal_sha256=SHA256,
        native_sha256=hashlib.sha256(b.table_bytes(folded)).hexdigest(),
        primitive_sites=len(sites), source_contracts=len(contracts),
        maximum_source_path_length=max(len(p) for p, op, arg in sites),
        source_binding=source_binding, emitter=emission,
        exact_native_edits=[[q, bit, w, d, n]
                            for (q, bit), (w, d, n) in sorted(EDITS.items())],
        arithmetic_box_rows_unchanged=True, local_cases=certificate['local_cases'],
        local_durations=certificate['durations'], symbolic_runtime=runtime,
        startup_literal_steps=start['literal_steps'],
        parent=dict(literal_sha256=b.EXPECTED_SHA, source_binding=parent_binding,
                    symbolic_runtime=parent_runtime, local_cases=old_cert['local_cases'],
                    startup_literal_steps=old_startup['literal_steps']),
        executable_certificate=True, new_kernel_checked_endpoint_theorem=False,
    )
    if args.export:
        dump(HERE / 'verification.json', result)
        dump(HERE / 'source.json', [dict(ordinal=i, path=''.join(map(str, p)), op=op,
                                       arg=arg, instruction=cfg[i])
                                   for i, (p, op, arg) in enumerate(sites)])
        dump(HERE / 'source_binding.json', source_binding)
        dump(HERE / 'local_fold_certificate.json', certificate)
        dump(HERE / 'startup_certificate.json', start)
        dump(HERE / 'emitter_tokens.json', b.word(tree))
        (HERE / 'unfolded202.native.tm').write_bytes(b.table_bytes(raw))
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
