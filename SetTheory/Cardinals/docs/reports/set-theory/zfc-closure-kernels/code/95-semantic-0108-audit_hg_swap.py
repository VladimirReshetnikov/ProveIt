#!/usr/bin/env python3
"""Check the exact gm -> hg source substitution and its 245-state blank run.

The optional affine check is universal over the inherited register-box
contracts. It is not a new proof-assistant endpoint or a state reduction.
"""
from functools import cache
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--affine', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = json.loads((ROOT / 'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((ROOT / 'inputs/semantic-symbols.json').read_text())
    inverse = {name: symbol for symbol, name in symbols.items()}
    baseline = json.loads((ROOT / 'results/state_reduction/candidate-zero6-k128.json').read_text())
    grammar = {w: (a, b) for w, a, b in baseline['rules']}
    names = {int(q): ''.join(inverse[c] for c in w)
             for q, w in source['flattened_semantic_words'].items()}
    by_ast = {int(i): names[int(q)]
              for q, i in source['sequence_ast_roots'].items()}

    @cache
    def changed(index, swap):
        if index in by_ast and by_ast[index] in grammar:
            return expand(by_ast[index], swap)
        row = source['ast_dag'][index]
        if row[0] == 'L':
            return 'L', tuple(row[1])
        return 'N', changed(row[1], swap), changed(row[2], swap)

    @cache
    def expand(word, swap):
        if word == 'gm' and swap:
            return 'N', expand('h', swap), expand('g', swap)
        if len(word) == 1:
            return changed(source['atoms'][symbols[word]]['ast'], swap)
        a, b = grammar[word]
        return 'N', expand(a, swap), expand(b, swap)

    def leaves(tree, path=''):
        if tree[0] == 'L':
            yield path, tree[1]
        else:
            yield from leaves(tree[1], path + '0')
            yield from leaves(tree[2], path + '1')

    codes = dict(inc='CI', dec='CD', brk='CB', cont='CC', halt='CH')

    def sites(tree):
        return [[p, codes[op[0]], op[1] if len(op) > 1 else None]
                for p, op in leaves(tree)]

    before = changed(source['original_ast'], False)
    after = changed(source['original_ast'], True)
    old_sites, new_sites = sites(before), sites(after)
    assert old_sites == json.loads((ROOT / 'reference/sites_logical.json').read_text())
    g = ('N', ('L', ('dec', 6)),
         ('N', ('L', ('inc', 5)), ('L', ('cont', 2))))
    assert expand('g', False) == g
    assert expand('m', False) == ('L', ('inc', 5))
    assert expand('h', False) == ('L', ('inc', 6))
    old_macro = ('N', g, ('L', ('inc', 5)))
    new_macro = ('N', ('L', ('inc', 6)), g)
    occurrences = []

    def compare(a, b, path=''):
        if a == old_macro:
            assert b == new_macro
            occurrences.append(path)
            return
        assert a[0] == b[0]
        if a[0] == 'L':
            assert a == b
        else:
            compare(a[1], b[1], path + '0')
            compare(a[2], b[2], path + '1')

    compare(before, after)
    assert len(occurrences) == 4
    assert len(old_sites) == len(new_sites) == 6460

    def table(path):
        result = {}
        for line in path.read_text().splitlines():
            if line and not line.startswith('#'):
                q, bit, write, direction, target = line.split()
                key = int(q), int(bit)
                assert key not in result
                assert direction in ('L', 'R')
                result[key] = int(write), 1 if direction == 'R' else -1, int(target)
        return result

    old_table = table(ROOT / 'reference/baseline245-old.tm')
    new_path = ROOT / 'results/hg-swap/hg245.tm'
    new_table = table(new_path)
    difference = {key: (old_table[key], new_table[key])
                  for key in old_table if old_table[key] != new_table[key]}
    assert difference == {(142, 0): ((0, 1, 37), (0, 1, 39)),
                          (142, 1): ((1, 1, 72), (1, 1, 37))}
    assert len(new_table) == 490 and len({q for q, b in new_table}) == 245

    expected = json.loads((ROOT / 'results/hg-swap/boot-result.json').read_text())
    ticks = expected['blank_steps']
    assert ticks == 416557
    q, head, ones = 95, 0, set()
    for _ in range(ticks):
        write, direction, q = new_table[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    assert q == 96 and head == expected['head']
    assert sorted(ones) == expected['all_one_positions']
    width = 2 * ticks + 3
    dense = bytearray(width)
    origin = pos = ticks + 1
    state = 95
    indexed = [None] * 512
    for (a, b), row in new_table.items():
        indexed[2 * a + b] = row
    for _ in range(ticks):
        write, direction, state = indexed[2 * state + dense[pos]]
        dense[pos] = write
        pos += direction
    assert state == q and pos - origin == head
    assert [i - origin for i, b in enumerate(dense) if b] == sorted(ones)
    assert min(ones) == head - 1
    header = min(x for x in ones if x >= head)
    assert header - head == 183
    values = []
    pos = header + 1
    last = max(ones)
    while pos <= last:
        assert pos not in ones and pos + 1 in ones
        first = pos + 1
        pos = first
        while pos in ones:
            pos += 1
        values.append(pos - first - 1)
    assert pos == last + 1 and len(values) == 178
    logical = [values[i] for i in PHYSICAL]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert values[9:] == [1] * 169

    result = dict(
        status='PASS_SOUND_SOURCE_SWAP_AND_FINITE_BLANK_AUDIT',
        working_states=245, state_reduction=False,
        table_sha256=hashlib.sha256(new_path.read_bytes()).hexdigest(),
        changed_rows=[[a, b, list(old), list(new)]
                      for (a, b), (old, new) in sorted(difference.items())],
        gm_occurrences=occurrences, leaves_before=6460, leaves_after=6460,
        guarded_instruction_cases=sum(2 if op == 'CD' else 1 for _, op, _ in new_sites),
        maximum_depth=max(len(p) for p, _, _ in new_sites),
        maximum_zero_run=max(len(z) for p, _, _ in new_sites for z in p.split('1')),
        mathematical_macro_identity='Both map (X,H)=(x,h) to (0,h+x+1) and terminate.',
        blank_steps=ticks, head=head, header=header, gap=header-head,
        logical_seed=logical, spare_count=169, spare_values=1,
        sparse_dense_exact_agreement=True,
        proof_assistant_endpoint=False)
    if args.affine:
        sys.path.insert(0, str(ROOT / 'reference/affine'))
        import parametric_prefix_affine as affine
        from parametric_affine_driver import check_sites
        affine.PADDING = 64
        affine_table = {(str(q), bit): (write, 'R' if direction == 1 else 'L', str(target))
                        for (q, bit), (write, direction, target) in new_table.items()}
        physical_sites = [(pc, op, PHYSICAL[r] if op in ('CI', 'CD') else r)
                          for pc, op, r in new_sites]
        result['conditional_universal_affine_audit'] = check_sites(
            affine, affine_table, physical_sites, 64)
        result['affine_scope'] = (
            'All 8391 guarded instructions, all n>=0 and register files satisfying the guard, '
            'under the unchanged inherited register-box contracts. This script does not '
            'reprove those contracts or provide a new proof-assistant endpoint.')
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
