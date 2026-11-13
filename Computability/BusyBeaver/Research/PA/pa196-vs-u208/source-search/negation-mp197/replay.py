#!/usr/bin/env python3
"""Rebuild and check the combined negation/MP experimental machine."""
import argparse
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[6]
PINS = {
    'pa_consistency_research_2026-11-13.zip': '466c804d54495d3347252a98788af021aecc459b041fcc1733b3adf1ff1e943b',
    'conpa_tm_comparison_and_reduction_search.zip': '46cd1a5f57f6c04f9a0379fa8dc042120bc6ae0329c370ca5d4a3d35907b5d48',
}
PREFIX_A = 'pa_consistency_research/'
PREFIX_B = 'conpa_tm_comparison_and_reduction_search/'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def decode_tree(module, tree):
    if tree == ['halt'] or tree == ('halt',):
        return module.interned(('halt', 0))
    need(isinstance(tree, (list, tuple)) and len(tree) == 2, 'bad source node')
    if isinstance(tree[0], str):
        need(tree[0] in {'inc', 'dec', 'breakTo', 'continueTo', 'halt'} and
             isinstance(tree[1], int), 'bad instruction')
        return module.interned((tree[0], tree[1]))
    return module.node(decode_tree(module, tree[0]), decode_tree(module, tree[1]))


def encode_tree(module, node):
    data = module.store[node]
    if not module.isnode(node):
        return data
    return encode_tree(module, data[1]), encode_tree(module, data[2])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--out-dir', type=Path, help='optional table, tree and site files')
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'archive checker requires Python without -O')
    archives = {name: REPO / 'docs/incoming' / name for name in PINS}
    for name, path in archives.items():
        need(digest(path.read_bytes()) == PINS[name], 'archive hash changed: ' + name)
    rot = load('pa196_rotations', HERE.parent / 'scan_rotations.py')
    zero = load('pa196_zero_transfer', HERE.parent / 'verify_zero_transfer.py')
    # The original source trie and the archive's original MP candidate must
    # agree exactly, not merely on its claimed size or branch location.
    with ZipFile(archives['conpa_tm_comparison_and_reduction_search.zip']) as z:
        mp = json.loads(z.read(PREFIX_B + 'sources/history209/mp_move_h_candidate.json'))
    old = rot.env['node163']
    replacement = rot.node(rot.env['node6'], rot.env['node147'])
    mp_source = rot.rewrite(rot.root, old, replacement)
    need(decode_tree(rot, mp['tree']) == mp_source,
         'incoming MP source rewrite differs')
    need(mp['original_source_states'] == 3812 and mp['source_states'] == 3789,
         'incoming MP source census differs')

    # Extract only the checker, its pinned inputs, and the candidate files.
    members = [
        'verification/check.py', 'verification/symbolic.py',
        'reference/pa196/PA196/Conjugacy.lean',
        'reference/pa196/PA196/Program.lean', 'reference/pa196/data/pa196.tm',
        'experiments/negation197/source.tree.json',
        'experiments/negation197/machine.native.tm',
    ]
    with tempfile.TemporaryDirectory(prefix='pa197-negation-mp-') as td:
        root = Path(td)
        with ZipFile(archives['pa_consistency_research_2026-11-13.zip']) as z:
            for rel in members:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(z.read(PREFIX_A + rel))
        original = decode_tree(rot, json.loads((root / members[-2]).read_text()))
        occurrences = [p for p, t in rot.node_occurrences(original) if t == old]
        need(occurrences == [(1, 0, 1, 0, 1, 0, 1, 1)], 'MP source occurrence changed')
        candidate = rot.rewrite(original, old, replacement)
        leaves = list(rot.leaf_occurrences(candidate))
        need((len(list(rot.leaf_occurrences(original))), len(leaves), rot.metric(candidate)) ==
             (3596, 3573, 159), 'combined source census changed')
        graph = rot.graph(candidate)
        independent_graph, _ = zero.interval_graph(rot, candidate)
        need(graph == independent_graph and all(None not in row for row in graph),
             'source control-flow resolvers differ or source exits')
        need(leaves[25][0] == (1, 0, 0, 0, 0, 0), 'startup site changed')
        # The source replacement requires a scratch-register entry invariant.
        # Audit the full joint zero/positive closure for both the MP-only and
        # combined sources; neither calculation assumes the desired invariant.
        joint = load('pa196_joint_mask', HERE.parent / 'verify_joint_mask.py')
        entries = [584, 686, 1759, 1861, 3119, 3193, 3428, 3611]
        def closure(graph0, shifted):
            seed = (25, 1)
            seen, queue = {seed}, deque([seed])
            while queue:
                pc, mask = queue.popleft()
                need(0 <= pc < len(graph0), 'joint-mask source exit')
                for state in joint.successors(graph0[pc], mask):
                    if state not in seen:
                        seen.add(state)
                        queue.append(state)
            for pc, mask in seen:
                need(all(state in seen for state in joint.successors(graph0[pc], mask)),
                     'joint-mask closure failed')
            selected = []
            for index, original_pc in enumerate(entries):
                pc = original_pc - (27 * index if shifted else 0)
                masks = sorted(mask for site, mask in seen if site == pc)
                need(masks and all((mask & (1 << 7)) == 0 for mask in masks),
                     'scratch register 7 not forced zero at entry')
                selected.append({'site': pc, 'mask_count': len(masks)})
            return {'site_mask_pairs': len(seen), 'entry_masks': selected,
                    'sha256': digest(json.dumps(sorted(seen), separators=(',', ':')).encode())}
        invariants = {'mp_only': closure(rot.graph(mp_source), False),
                      'negation_and_mp': closure(graph, True)}
        need([invariants['mp_only']['site_mask_pairs'],
              invariants['negation_and_mp']['site_mask_pairs']] == [274596, 258660],
             'joint-mask closure census changed')
        sys.path.insert(0, str(root / 'verification'))
        check = load('incoming_combined_checker', root / members[0])
        table = check.parse(root / members[-1])
        need(table[164, 1] == (1, 'R', 98), 'MP table input row changed')
        table[164, 1] = (1, 'R', 130)
        # Verify the change also agrees with the separately supplied MP table.
        mp_rows = {(q, b): (w, d, n) for q, b, w, d, n in mp['table']}
        need(mp_rows[164, 1] == table[164, 1], 'incoming MP table disagrees')
        table_text = ''.join(f'{q} {b} {w} {d} {n}\n'
                             for (q, b), (w, d, n) in sorted(table.items()))
        tree_text = json.dumps(encode_tree(rot, candidate)) + '\n'
        site_ops = {'inc': 'CI', 'dec': 'CD', 'breakTo': 'CB',
                    'continueTo': 'CC', 'halt': 'CH'}
        sites = [[''.join(map(str, path)), site_ops[rot.store[t][0]], rot.store[t][1]]
                 for path, t in leaves]
        site_text = json.dumps(sites) + '\n'
        need((HERE / 'machine.native.tm').read_text() == table_text and
             (HERE / 'source.tree.json').read_text() == tree_text,
             'retained candidate differs from reconstructed files')
        result = check.run('negation_mp197', table, encode_tree(rot, candidate))
        need(result == {'name': 'negation_mp197', 'working_states': 197, 'rows': 394,
                        'engine_agreement_rows': 42, 'startup_steps': 58154,
                        'symbolic': {'sites': 3573, 'cases': 4641, 'max_symbolic_steps': 515},
                        'passed': True}, 'symbolic contract or startup changed')
        # The input has exactly the dense reachable working-state census.
        seen, work = {74}, [74]
        while work:
            state = work.pop()
            for bit in (0, 1):
                target = table[state, bit][2]
                if target != 254 and target not in seen:
                    seen.add(target)
                    work.append(target)
        need(len(seen) == 197, 'reachable state census changed')
        if args.out_dir:
            args.out_dir.mkdir(parents=True, exist_ok=True)
            (args.out_dir / 'machine.native.tm').write_text(table_text)
            (args.out_dir / 'source.tree.json').write_text(tree_text)
            (args.out_dir / 'sites.json').write_text(site_text)
            (args.out_dir / 'machine-with-start.native.tm').write_text('#! start 74\n' + table_text)
        receipt = {'archive_sha256': PINS, 'imported_mp_original_source_checked': True,
                   'negation_source_sites': 3596, 'combined_source_sites': 3573,
                   'combined_source_internal_nodes': rot.metric(candidate),
                   'mp_subtree_path': ''.join(map(str, occurrences[0])),
                   'independent_source_graph_resolvers_agree': True,
                   'scratch_register_entry_invariants': invariants,
                   'table_row_change_native': [164, 1, [1, 'R', 98], [1, 'R', 130]],
                   'table_sha256': digest(table_text.encode()),
                   'source_tree_sha256': digest(tree_text.encode()),
                   'sites_sha256': digest(site_text.encode()),
                   'graph_reachable_working_states': len(seen),
                   'archive_symbolic_and_startup_result': result,
                   'scope': 'Experimental 197-state machine; executable symbolic contracts are not a PA proof.'}
        text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
        print(text, end='')
        if args.output:
            args.output.write_text(text)


if __name__ == '__main__':
    main()
