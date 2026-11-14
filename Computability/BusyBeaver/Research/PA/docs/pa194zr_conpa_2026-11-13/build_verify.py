#!/usr/bin/env python3
"""Reconstruct PA194ZR and verify its new source/physical facts.

Run without Python -O. Ordinary finite certificates, not a new Lean theorem.
The inherited symbolic runtime uses the unchanged register-box lemmas.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
REF = HERE / 'reference_cs'
sys.path.insert(0, str(REF))
import compiler as c
import baseline_tools as b

ORIGINAL_NODES = c.raw_nodes

BASE_SHA = '00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b'
RETURN_SITES = [3, 9, 3526, 3532, 3544, 3550, 3627, 3633]
CHANGED_SITES = RETURN_SITES + [3553]
CHANGED_SITES.sort()
REGION = set(range(10)) | set(range(3523, 3634)) | set(range(3638, 3646))
EDITS = {(103, 1): (1, True, 17), (2066, 1): (1, True, 17)}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def normalized(obj):
    return json.loads(json.dumps(obj))


def cs_nodes(original):
    def nodes():
        ns = original()
        ns['node163'] = ('node6', 'node147')
        ns['node170'] = (('node36', ('node167', 'node145')), 'node56')
        ns['node171'] = ('node170', (('leaf', 'inc', 5), ('leaf', 'continueTo', 3)))
        return ns
    return nodes


def replace_close(t):
    if t == ('leaf', 'breakTo', 1):
        return ('leaf', 'dec', 3)
    if c.isnode(t):
        return replace_close(t[0]), replace_close(t[1])
    return t


def edges(cfg):
    for pc, ins in enumerate(cfg):
        if ins[0] == 'inc':
            yield pc, 'next', ins[2]
        elif ins[0] == 'dec':
            yield pc, 'zero', ins[2]
            yield pc, 'positive', ins[3]
        elif ins[0] == 'jump':
            yield pc, 'jump', ins[1]
        else:
            assert ins == ('halt',)


def region_certificate(old, new):
    assert len(REGION) == 129 and 25 not in REGION
    assert set(CHANGED_SITES) <= REGION
    changes = [i for i in range(len(old)) if old[i] != new[i]]
    assert changes == CHANGED_SITES
    changes_data = []
    for i in changes:
        assert old[i][0] == 'jump'
        assert new[i] == ('dec', 3, old[i][1], i + 1)
        changes_data.append({'site': i, 'before': old[i], 'after': new[i]})
    all_entries = []
    for name, cfg in [('old', old), ('new', new)]:
        entries = []
        for i in REGION:
            assert cfg[i][:2] != ('inc', 3)
        for pc, branch, target in edges(cfg):
            assert 0 <= target < len(cfg)
            if pc not in REGION and target in REGION:
                assert cfg[pc][0:2] == ('dec', 3) and branch == 'zero'
                entries.append([pc, target])
        assert entries == [[48, 3638], [49, 3554], [3519, 3523]]
        all_entries.append({'program': name, 'entries': entries})
    return {
        'logical_register': 3,
        'region_sites': sorted(REGION),
        'region_cardinality': 129,
        'initial_source_site': 25,
        'initial_source_site_outside_region': True,
        'no_increment_of_register_in_region': True,
        'all_external_entries_are_zero_decrement_edges': all_entries,
        'changes': changes_data,
        'source_statement': 'For any initial register store at site 25, both source programs have identical complete source configurations at every step.',
        'proof': 'Induction on execution: entry to the region sets R3=0; all region instructions preserve R3=0. Every changed instruction is therefore a zero decrement with exactly the old jump target and unchanged registers.',
    }


def construct(full=True):
    assert __debug__ and not sys.flags.optimize, 'Run without -O'
    c.raw_nodes = cs_nodes(ORIGINAL_NODES)
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    old_tree = c.read_grammar(REF / 'inputs/pa194.grammar.json')
    old_sites, old_cfg, old_contracts = c.source(old_tree)
    assert normalized(old_cfg) == json.loads((REF / 'inputs/pa194CS.instructions.json').read_text())
    old_site_json = [[''.join(map(str, p)), op, arg] for p, op, arg in old_sites]
    assert old_site_json == json.loads((REF / 'inputs/pa194CS.sites.json').read_text())
    parent_nodes = c.raw_nodes
    def changed_nodes():
        ns = parent_nodes()
        assert ns['node1'] == ('node0', ('leaf', 'breakTo', 1))
        ns['node1'] = ('node0', ('leaf', 'dec', 3))
        return ns
    c.raw_nodes = changed_nodes
    tree = replace_close(old_tree)
    sites, cfg, contracts = c.source(tree)
    assert len(sites) == len(old_sites) == 3646
    assert len(contracts) == 4754
    assert [p for p, _, _ in sites] == [p for p, _, _ in old_sites]
    source_proof = region_certificate(old_cfg, cfg)
    base_bytes = (REF / 'inputs/pa194CS.native.tm').read_bytes()
    assert sha(base_bytes) == BASE_SHA
    parent = b.read_table(REF / 'inputs/pa194CS.native.tm')
    rows = dict(parent)
    rows.update(EDITS)
    assert len(rows) == 388
    controls = {q for q, bit in rows}
    assert len(controls) == 194 and 74 in controls and 254 not in controls
    assert set(rows) == {(q, bit) for q in controls for bit in (0, 1)}
    assert all(w in (0, 1) and d in (False, True) and n in controls | {254}
               for w, d, n in rows.values())
    assert {qb: act for qb, act in rows.items() if act != parent[qb]} == EDITS
    assert all(rows[q, bit] == parent[q, bit] for q in c.BOXSTATES for bit in (0, 1))
    graph_seen, todo = {74}, [74]
    for q in todo:
        for bit in (0, 1):
            n = rows[q, bit][2]
            if n != 254 and n not in graph_seen:
                graph_seen.add(n); todo.append(n)
    assert graph_seen == controls
    startup = b.startup(rows, sites[25][0])
    assert startup['steps'] == 59816
    dense, labels = b.dense_table(rows, 194)
    result = {
        'status': 'PASS',
        'family': 'PA194ZR',
        'working_states': 194,
        'transition_rows': 388,
        'graph_reachable_working_states': 194,
        'start_native': 74,
        'halt_native': 254,
        'start_dense': 0,
        'halt_dense': 194,
        'source_sites': 3646,
        'source_branch_contracts': 4754,
        'source_changed_sites': CHANGED_SITES,
        'source_cfg_region_proof': source_proof,
        'arithmetic_box_rows_unchanged': True,
        'changed_native_rows': [[q, bit, list(parent[q, bit]), list(act)] for (q, bit), act in sorted(EDITS.items())],
        'startup': startup,
        'base_native_sha256': BASE_SHA,
        'native_sha256': sha(b.table_text(rows).encode()),
        'dense_sha256': sha(b.table_text(dense).encode()),
        'full_symbolic_runtime_checked': full,
        'new_kernel_checked_endpoint': False,
    }
    if full:
        runtime = c.validate(rows, contracts)
        assert runtime['ok'], runtime
        result['symbolic_runtime'] = runtime
    files = {
        'machine/pa194zr.native.tm': b.table_text(rows),
        'machine/pa194zr.tm': b.table_text(dense),
        'machine/labels.json': json.dumps(labels, indent=2) + '\n',
        'source/sites.json': json.dumps([[''.join(map(str, p)), op, arg] for p, op, arg in sites], indent=2) + '\n',
        'source/instructions.json': json.dumps(cfg, indent=2) + '\n',
        'proof/region_certificate.json': json.dumps(source_proof, indent=2) + '\n',
        'proof/startup_certificate.json': json.dumps(startup, indent=2) + '\n',
    }
    if full:
        files['proof/validation.json'] = json.dumps(result, indent=2) + '\n'
    return files, result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true', help='Omit only the full symbolic runtime pass.')
    ap.add_argument('--export', action='store_true', help='Write the generated tables and evidence.')
    args = ap.parse_args()
    files, result = construct(full=not args.quick)
    for name, text in files.items():
        path = HERE / name
        if args.export:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        else:
            assert path.read_text() == text, 'Generated file differs: ' + name
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
