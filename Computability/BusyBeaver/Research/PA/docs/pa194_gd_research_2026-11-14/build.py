#!/usr/bin/env python3
"""Build the GD, GDH, GDHS 194-state machines from the pinned source inputs.

Python 3.10+, standard library only. All verification assertions are mandatory.
The independent literal-row verifier and the arithmetic calibration are separate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'construction'))
import compiler as c
import support as b

INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)
EXPECTED = {
    'GD': '1362fe8f264656e5b6d3e88666c0c88a34883c4d3cc5e9f2b4da9f9f6e8e595e',
    'GDH': 'e11b587cdb7d620adc9ce086467931f2d9db453f56231c5829e9f8c71c04eed1',
    'GDHS': '7b69655c9115d226f23be4cd70303650f894a97d195c53139f72e1c937cdda58',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def input_check():
    provenance = json.loads((HERE / 'PROVENANCE.json').read_text())
    for item in provenance['inputs']:
        content = (HERE / item['file']).read_bytes()
        assert sha(content) == item['sha256'], ('input identity', item['file'])
        git_blob = hashlib.sha1(('blob ' + str(len(content)) + '\0').encode() + content).hexdigest()
        assert git_blob == item['source_git_blob'], ('Git identity', item['file'])

def source_nodes():
    nodes = {}
    for line in (HERE / 'inputs/Program.lean').read_text().splitlines():
        match = re.match(r'def (\w+) : Tree := \.node (.*)', line)
        if not match:
            continue
        tokens = re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b', match[2])
        children = [name if name else ('leaf', op, int(arg) if arg else None)
                    for op, arg, name in tokens]
        assert len(children) == 2
        nodes[match[1]] = tuple(children)
    return nodes

def normalize(tree):
    if tree == 'node60':
        return INC, INC
    if tree == 'node61':
        return (INC, INC), (INC, INC)
    return tuple(normalize(t) for t in tree) if c.isnode(tree) else tree

def word(tree):
    return word(tree[0]) + word(tree[1]) if c.isnode(tree) else [tree]

def substitute(tree, values):
    stream = iter(values)
    def go(t):
        return tuple(go(z) for z in t) if c.isnode(t) else next(stream)
    answer = go(tree)
    assert next(stream, None) is None
    return answer

def encoded_grammar(tree):
    rules, indices = {}, {}
    def go(t):
        if not c.isnode(t):
            return t
        if t in indices:
            return indices[t]
        name = 'g' + str(len(indices))
        indices[t] = name
        rules[name] = [go(z) for z in t]
        return name
    root = go(tree)
    return {'root': root, 'rules': rules}

def new_grammar():
    primary = normalize(c.read_grammar(HERE / 'inputs/primary.grammar.json'))
    diagonal = normalize(c.read_grammar(HERE / 'inputs/diagonal_D.grammar.json'))
    old, new = word(primary), word(diagonal)
    assert len(old) == len(new) == 190
    assert [(i, a, z) for i, (a, z) in enumerate(zip(old, new)) if a != z] == [
        (121, 'node70', 'node55'), (122, 'node70', 'node55'),
        (123, 'node70', 'node55'), (189, BREAK, ('leaf', 'dec', 4))]
    # Change only the saved-generalization binder from the incoming offset D
    # to the explicit AX parameter A. Restore an ordinary structural exit.
    new[1] = 'node70'
    new[-1] = BREAK
    assert [(i, a, z) for i, (a, z) in enumerate(zip(old, new)) if a != z] == [
        (1, 'node55', 'node70'), (121, 'node70', 'node55'),
        (122, 'node70', 'node55'), (123, 'node70', 'node55')]
    return substitute(diagonal, new), substitute(primary, new)

def fixed_part(family):
    rows = b.read_table(HERE / 'inputs/primary.raw.native.tm')
    nodes = source_nodes()
    # Successful MP copies the consequent without pushing a dummy zero.
    rows[164, 1] = (1, True, 114)
    nodes['node163'] = ('node6', 'node54')
    if family in ('GDH', 'GDHS'):
        rows.update({(38, 0): (0, True, 11), (38, 1): (1, True, 122),
                     (214, 0): (0, True, 312), (214, 1): (1, True, 20),
                     (312, 0): (0, True, 188)})
        nodes['node170'] = (('node36', ('node167', 'node145')), 'node57')
    if family == 'GDHS':
        rows.update({(214, 1): (1, True, 30), (310, 1): (1, True, 331),
                     (331, 0): (0, True, 63), (331, 1): (1, False, 73)})
        nodes['node170'] = (('node36', ('node167', 'node145')), 'node56')
        nodes['node171'] = ('node170', (('leaf', 'inc', 5), ('leaf', 'continueTo', 3)))
    assert nodes['node22'] == (('leaf', 'dec', 8), BREAK)
    return rows, nodes

def build(family, output, full=True):
    assert __debug__, 'Run without Python -O.'
    input_check()
    rows, nodes = fixed_part(family)
    c.machine = lambda: (rows, [])
    c.raw_nodes = lambda: nodes
    c.MACROS[(INC, INC)] = 99
    c.MACROS[((INC, INC), (INC, INC))] = 190
    tree, reference = new_grammar()
    raw, _, shape = c.build(tree)
    assert len(shape) == 69
    sites, instructions, contracts = c.source(tree)
    _, reference_instructions, _ = c.source(reference)
    assert instructions == reference_instructions, 'Reassociation changes a source successor.'
    folds = json.loads((HERE / 'inputs' / ('folds_' + family + '.json')).read_text())
    child, aliases = b.apply_folds(raw, folds)
    local = b.check_local_folds(raw, child, aliases, folds)
    assert len(child) == 388 and len(local['cases']) == 4 * len(folds)
    primary = b.read_table(HERE / 'inputs/primary.raw.native.tm')
    assert all(child[q, bit] == primary[q, bit] for q in c.BOXSTATES for bit in (0, 1))
    startup = b.startup(child, sites[25][0])
    runtime = c.validate(child, contracts) if full else None
    assert not full or runtime['ok']
    dense, labels = b.dense_table(child, 194)
    dense_bytes = b.table_text(dense).encode()
    assert sha(dense_bytes) == EXPECTED[family], 'Output table identity'
    output.mkdir(parents=True, exist_ok=True)
    for name, table in [('machine.native.tm', child), ('raw.native.tm', raw), ('machine.tm', dense)]:
        (output / name).write_text(b.table_text(table))
    for name, value in [('nodes.json', nodes), ('sites.json', [[''.join(map(str,p)), op, a] for p,op,a in sites]),
                        ('instructions.json', instructions), ('grammar.json', encoded_grammar(tree)),
                        ('folds.json', folds), ('labels.json', labels), ('local_cases.json', local)]:
        dump(output / name, value)
    result = {'name': 'PA194' + family, 'states': 194, 'transitions': 388,
              'start': 0, 'halt': 194, 'native_start': 74, 'native_halt': 254,
              'raw_states': len(raw)//2, 'AX_readers': len(shape), 'folds': len(folds),
              'source_sites': len(sites), 'outcomes': len(contracts),
              'complete_resolved_graph_matches_reference_shape': True,
              'source_word_changes_from_primary': [1,121,122,123],
              'zero_test_specializations': False, 'arithmetic_box_rows_unchanged': True,
              'source_contracts_replayed': full, 'symbolic_validation': runtime,
              'local_cases': len(local['cases']), 'startup': startup,
              'sha256': sha(dense_bytes), 'native_sha256': sha(b.table_text(child).encode()),
              'proof_scope': 'Executable finite and symbolic certificates; see the report for the mathematical iPRA argument. No new Lean endpoint.'}
    dump(output / 'receipt.json', result)
    print(json.dumps({k:result[k] for k in ('name','states','raw_states','AX_readers','folds','source_sites','outcomes','sha256')}), flush=True)
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=['GD','GDH','GDHS','all'], default='all')
    parser.add_argument('--output', type=Path, required=True, help='Fresh destination directory.')
    parser.add_argument('--quick', action='store_true', help='Skip the universal symbolic source contracts.')
    args = parser.parse_args()
    families = ['GD','GDH','GDHS'] if args.family == 'all' else [args.family]
    for family in families:
        build(family, args.output / family, not args.quick)
