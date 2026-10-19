#!/usr/bin/env python3
"""Audit the four closed increment/drain replacements independently.

No candidate builder or source-rotation module is imported. The finite check
verifies exact contextual substitution, every external entry and exit, the
literal internal graphs, and equality of the entire collapsed program.
The natural-number induction for the macro's (a,b)->(a+b+1,0) contract is
given in the accompanying mathematical report, not inferred from sampling.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def need(value, message):
    if not value:
        raise ValueError(message)


OLD = ((('CD', 6), (('CI', 5), ('CC', 2))), ('CI', 5))
NEW = (('CI', 5), (('CD', 6), ('CC', 2)))


def source_tree(rows):
    leaves = {p: (op, arg) for p, op, arg in rows}
    need(len(leaves) == len(rows), 'Repeated leaf')
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    need(not (set(leaves) & prefixes), 'A leaf contains another leaf')
    need('' in prefixes, 'Missing root')
    for p in prefixes:
        need(all(p + c in prefixes or p + c in leaves for c in '01'), 'Incomplete tree')

    def descend(p):
        if p in leaves:
            return leaves[p]
        return descend(p + '0'), descend(p + '1')
    return descend(''), leaves


def flatten(t, p=''):
    if isinstance(t[0], str):
        return [[p, *t]]
    return flatten(t[0], p + '0') + flatten(t[1], p + '1')


def graph(leaves):
    maximum = max(map(len, leaves))

    def locate(word):
        for depth in range(1, maximum + 1):
            p = (word + '0' * maximum)[:depth]
            if p in leaves:
                need('1' not in word[depth:], 'Nonzero unused address tail')
                return p
        raise ValueError('Missing decoded leaf')

    def following(word):
        i = word.rfind('0')
        return '' if i < 0 else word[:i] + '1' + '0' * (len(word) - i - 1)

    def cut(word, bit, count):
        positions = [i for i, b in enumerate(word) if b == bit]
        return word[:positions[-count]] if len(positions) >= count else ''

    out = {}
    for p, (op, arg) in leaves.items():
        if op == 'CI':
            out[p] = ('INC', arg, locate(following(p)))
        elif op == 'CD':
            out[p] = ('DEC', arg, locate(following(p)), locate(following(cut(p, '0', 1))))
        elif op == 'CB':
            out[p] = ('JUMP', locate(following(cut(p, '0', arg))))
        elif op == 'CC':
            out[p] = ('JUMP', locate(cut(p, '1', arg)))
        else:
            need(op == 'CH' and arg is None, 'Unknown operation')
            out[p] = ('HALT',)
    return out, locate('')


def audit(original, candidate):
    original_tree, old_leaves = source_tree(original)
    candidate_tree, new_leaves = source_tree(candidate)
    replacements = []

    def rewrite(t, p=''):
        if t == OLD:
            replacements.append(p)
            return NEW
        if isinstance(t[0], str):
            return t
        return rewrite(t[0], p + '0'), rewrite(t[1], p + '1')

    expected = rewrite(original_tree)
    need(expected == candidate_tree, 'There is a change outside the four exact macros')
    need(len(replacements) == 4, 'Wrong occurrence census')
    old_graph, old_entry = graph(old_leaves)
    new_graph, new_entry = graph(new_leaves)

    def collapse(cfg, variant, entry):
        inside, nodes = {}, {}
        exits = {}
        for p in replacements:
            if variant == 'old':
                need(cfg[p + '00'] == ('DEC', 6, p + '010', p + '1'), 'Old decrement graph')
                need(cfg[p + '010'] == ('INC', 5, p + '011'), 'Old increment graph')
                need(cfg[p + '011'] == ('JUMP', p + '00'), 'Old loop return')
                need(cfg[p + '1'][:2] == ('INC', 5), 'Old final increment')
                first, exit_path = p + '00', cfg[p + '1'][2]
                body = [p + x for x in ('00', '010', '011', '1')]
            else:
                need(cfg[p + '0'] == ('INC', 5, p + '10'), 'New increment graph')
                need(cfg[p + '10'][:3] == ('DEC', 6, p + '11'), 'New decrement graph')
                need(cfg[p + '11'] == ('JUMP', p + '0'), 'New loop return')
                first, exit_path = p + '0', cfg[p + '10'][3]
                body = [p + x for x in ('0', '10', '11')]
            for q in body:
                need(q not in inside, 'Overlapping macro replacements')
                inside[q] = (p + '#H', q == first)
            exits[p + '#H'] = exit_path

        def target(p):
            if p not in inside:
                return p
            name, first = inside[p]
            need(first, 'An external transition enters the middle of the macro')
            return name

        for p, row in cfg.items():
            if p in inside:
                continue
            if row[0] == 'INC':
                nodes[p] = row[:2] + (target(row[2]),)
            elif row[0] == 'DEC':
                nodes[p] = row[:2] + (target(row[2]), target(row[3]))
            elif row[0] == 'JUMP':
                nodes[p] = ('JUMP', target(row[1]))
            else:
                nodes[p] = row
        for name, exit_path in exits.items():
            nodes[name] = ('TRANSFER_PLUS_ONE', 5, 6, target(exit_path))
        return nodes, target(entry)

    old_collapsed = collapse(old_graph, 'old', old_entry)
    new_collapsed = collapse(new_graph, 'new', new_entry)
    need(old_collapsed == new_collapsed, 'Collapsed programs differ')
    need(len(original) == 5125 and len(candidate) == 5121, 'Wrong leaf counts')
    return {'status': 'INDEPENDENT_H_CONTEXT_AND_ALL_ENTRIES_PASS',
            'old_leaves': len(original), 'new_leaves': len(candidate),
            'new_guarded_cases_including_halt': sum(2 if r[0] == 'DEC' else 1 for r in new_graph.values()),
            'replacement_prefixes': replacements,
            'collapsed_control_points': len(old_collapsed[0]),
            'all_external_entries_and_exits_checked': True,
            'all_other_primitive_operations_and_edges_checked': True,
            'ordinary_loop_induction_required': '(R5,R6)=(a,b) maps to(a+b+1,0), for all natural a,b; every other register is unchanged.',
            'scope': 'Finite syntactic premises for the closed-macro replacement theorem; independent of native machine correctness.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k230-sites', type=Path, required=True)
    parser.add_argument('--h-sites', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    a = parser.parse_args()
    ops = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB', 'EContinue': 'CC', 'EHalt': 'CH'}
    original = []
    for p, instruction in json.loads(a.k230_sites.read_bytes()):
        xs = instruction.split()
        need(xs[0] in ops and len(xs) in (1, 2), 'Bad original source descriptor')
        original.append([p, ops[xs[0]], int(xs[1]) if len(xs) == 2 else None])
    receipt = audit(original, json.loads(a.h_sites.read_bytes()))
    receipt['sha256'] = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                         for name, path in [('original', a.k230_sites), ('candidate', a.h_sites),
                                            ('checker', Path(__file__))]}
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
