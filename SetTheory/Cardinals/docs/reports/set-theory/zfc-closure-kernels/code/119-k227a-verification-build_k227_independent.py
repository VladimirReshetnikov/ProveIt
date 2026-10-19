#!/usr/bin/env python3
"""Build the exact227-state K-theory candidate from the verified228 basis.

The construction uses one closed source rotation, right184/181, and one
context-dependent split fold deleting218. It introduces no fresh state.

Python3.10+ standard library. Run with assertions enabled. The sibling
source_tools.py is an unchanged copy of ProveIt's build_zfc235.py; this
builder uses only its source/table helpers. verify_split_fold.py supplies
an independent exhaustive two-cell proof of the binary split fold.

Usage:
  python3 -B build_k227.py --baseline-table k228_old.tm \
      --baseline-source sites229.json --output-dir OUTPUT

The separate universal runtime certificate proves the correspondence of
the final table with the rotated source. This builder does not replace it.
"""
import argparse
import json
import sys
from pathlib import Path

import source_tools as b
import verify_split_fold

TABLE228 = '7f5153ac9360cbab06a4c8ce0a01d55228a4f4e32dcd83a3234d5ef94c2f35a6'
SOURCE228 = '61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b'
ROTATED228 = 'e1f3ecd469a0048661bbd3bdb938631310bb5be81463ca004fff97e38be8681f'
TABLE227 = '175d6d4df7b988b45253e0a3bcb2651648b55a0ca1efddd4d5c6100ff71b8f46'
SOURCE227 = '055e6d5426590a1d25907202197809ab1d921ab3b1108a6d89b85db5ea3ab329'
START, DISPATCH, HALT = 95, 96, 254


def require(condition, message):
    if not condition:
        raise ValueError(message)


def construction(baseline_raw, source_raw):
    require(b.sha(baseline_raw) == TABLE228, 'Wrong pinned228 table bytes')
    require(b.sha(source_raw) == SOURCE228, 'Wrong pinned228 source bytes')
    old = b.read_table(baseline_raw)
    require(len(old) == 456, 'Expected228 input states')
    root = b.tree(json.loads(source_raw))
    initial_metrics = b.metrics(root)
    ordered, reference, initial = b.graph(b.sites(root))
    mapping, inverse = b.decoder_mapping(root, old)
    incoming_inner = [list(row) for row, (_, _, target) in sorted(old.items())
                      if target == 181]
    require(incoming_inner == [[184, 0]], '181 has a second incoming port')
    before_rows = [dict(row=[q, bit], transition=old[q, bit])
                   for q in (181, 184) for bit in (0, 1)]

    rotated_root, basis, rotation = b.stage(root, old, 184, 181, 'right')
    source = b.sites(rotated_root)
    word, graph, entry = b.graph(source)
    require([r[1:] for r in word] == [r[1:] for r in ordered],
            'Source instruction order changed')
    require(graph == reference and entry == initial,
            'A source guarded successor changed')
    guarded_cases = sum(2 if r[0] == 'DEC' else 1 for r in graph)
    require(len(source) == 5121 and guarded_cases == 6656,
            'Unexpected source or guarded-case census')
    require(rotation['paths'] == ['1110100100101011'] and
            rotation['chunk_leaf_counts'] == [52, 54, 189],
            'Unexpected rotated source occurrence')
    final_metrics = b.metrics(rotated_root)
    require(final_metrics == dict(dag_nodes=212, leaf_occurrences=5121,
                                 maximum_depth=40, maximum_zero_run=6),
            'Unexpected227 source metrics')
    basis_raw = b.encode(basis)
    new_source_raw = b.json_bytes(source, compact=True)
    require(b.sha(basis_raw) == ROTATED228, 'Wrong rotated228 table bytes')
    require(b.sha(new_source_raw) == SOURCE227, 'Wrong227 source bytes')

    # Context split: original218 entrants leave their written bit immediately
    # left of the head. Route left0 through242 and left1 through179.
    incoming_drop = [(row, w, d) for row, (w, d, target) in sorted(basis.items())
                     if target == 218]
    require(all(d == 1 for _, w, d in incoming_drop), 'A218 arrival moves left')
    candidate = {(q, bit): (w, d, (242 if w == 0 else 179) if target == 218 else target)
                 for (q, bit), (w, d, target) in basis.items() if q != 218}
    candidate[179, 1] = (1, -1, 215)
    candidate[242, 0] = (0, -1, 165)
    candidate[242, 1] = (1, -1, 195)
    candidate_raw = b.encode(candidate)
    require(len(candidate) == 454 and b.sha(candidate_raw) == TABLE227,
            'Wrong227 table bytes')
    split_fold = verify_split_fold.verify(basis_raw, candidate_raw)

    states = {q for q, bit in candidate}
    order = [START] + sorted(states - {START})
    renumber = {q: i for i, q in enumerate(order)} | {HALT: 227}
    canonical = {(renumber[q], bit): (w, d, renumber[target])
                 for (q, bit), (w, d, target) in candidate.items()}
    require(set(canonical) == {(q, bit) for q in range(227) for bit in (0, 1)},
            'Canonical table is not a total227-state table')
    canonical_raw = b.encode(canonical, start=0)
    require({target for w, d, target in canonical.values()} - set(range(227)) == {227},
            'Canonical halt is not227')

    source_certificate = dict(
        format='k227-closed-source-rotation-certificate-v1',
        status='PASS_ALL_SOURCE_GUARDS',
        baseline_table_sha256=TABLE228, baseline_source_sha256=SOURCE228,
        rotated_basis_sha256=ROTATED228, source_sha256=SOURCE227,
        stages=[dict(number=1, **rotation)],
        preconditions=dict(
            pure_decoder_rows=before_rows,
            unique_tree_nodes_per_state={str(q): len(inverse[q]) for q in (181, 184)},
            inner_state_incoming_rows=incoming_inner,
            source_chunks_have_no_escaping_break_continue_or_halt=True),
        initial_metrics=initial_metrics, final_metrics=final_metrics,
        source_instructions_compared=len(source), guarded_cases_compared=guarded_cases,
        identical_instruction_order=True, identical_guarded_successors=True,
        identical_entry_instruction=True,
        source_graph_sha256=b.sha(b.json_bytes(reference, compact=True)),
        changed_leaf_paths=sum(a[0] != c[0] for a, c in zip(ordered, word)),
        scope=('Every source configuration over arbitrary natural registers. '
               'The source instruction and guarded successor graphs agree '
               'under the order-preserving leaf bijection. Binary runtime '
               'correspondence is verified separately.'))
    renumbering = dict(old_to_new=renumber, new_to_old=order + [HALT],
                       start_old=START, start_new=0,
                       dispatcher_old=DISPATCH, dispatcher_new=renumber[DISPATCH],
                       halt_old=HALT, halt_new=227)
    receipt = dict(
        format='k227-exact-construction-v1',
        status='EXACT_CONSTRUCTION_SOURCE_GRAPH_AND_SPLIT_FOLD_PASS',
        working_states=227, transition_rows=454,
        baseline_working_states=228, deleted_states=[218], added_states=[],
        inherited_start=START, inherited_dispatcher=DISPATCH, inherited_halt=HALT,
        canonical_start=0, canonical_dispatcher=renumber[DISPATCH], canonical_halt=227,
        baseline_sha256=TABLE228, baseline_source_sha256=SOURCE228,
        rotated_basis_sha256=ROTATED228, inherited_sha256=TABLE227,
        canonical_sha256=b.sha(canonical_raw), source_sha256=SOURCE227,
        rotation_count=1, all_tape_macro_cases=8,
        all_changed_surviving_rows=[dict(row=[q, bit], before=old[q, bit], after=candidate[q, bit])
                                   for q, bit in sorted(candidate) if candidate[q, bit] != old[q, bit]],
        deleted_rows=[dict(row=[218, bit], before=old[218, bit]) for bit in (0, 1)],
        scope=('Exact table construction, source guard graph preservation, '
               'and an arbitrary-tape proof of the split fold. The unbounded '
               'binary runtime and blank startup certificates are separate.'))
    source_text = ''.join(f'{p} {op} {-1 if register is None else register}\n'
                          for p, op, register in source).encode()
    files = {
        'basis228_rotated_old.tm': basis_raw,
        'k227_old.tm': candidate_raw,
        'k227.tm': canonical_raw,
        'sites_logical.json': new_source_raw,
        'sites.txt': source_text,
        'source_rotation_certificate.json': b.json_bytes(source_certificate),
        'split_fold_certificate.json': b.json_bytes(split_fold),
        'renumbering227.json': b.json_bytes(renumbering),
        'construction227.json': b.json_bytes(receipt),
    }
    return files, receipt


def discovery_isomorphism(discovery_raw, clean_raw):
    old = b.read_table(discovery_raw)
    clean = b.read_table(clean_raw)
    permutation = {74: 242, 300: 74}
    rho = lambda q: permutation.get(q, q)
    require(len({rho(q) for q, bit in old}) == 227,
            'Discovery renaming is not injective')
    renamed = {(rho(q), bit): (w, d, rho(target))
               for (q, bit), (w, d, target) in old.items()}
    require(renamed == clean and rho(START) == START and rho(HALT) == HALT,
            'Discovery and clean tables are not exactly isomorphic')
    return dict(status='EXACT_TABLE_ISOMORPHISM_PASS',
                discovery_sha256=b.sha(discovery_raw), clean_sha256=b.sha(clean_raw),
                changed_state_names=permutation, all_other_state_names_unchanged=True,
                transition_rows_compared=454, working_states=227,
                start_and_halt_preserved=True,
                scope='Exact state renaming preserves every binary-tape run step for step.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-table', type=Path, required=True)
    parser.add_argument('--baseline-source', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--discovery-table', type=Path)
    parser.add_argument('--discovery-source', type=Path)
    args = parser.parse_args()
    files, receipt = construction(args.baseline_table.read_bytes(),
                                  args.baseline_source.read_bytes())
    if args.discovery_table:
        isomorphism = discovery_isomorphism(args.discovery_table.read_bytes(),
                                            files['k227_old.tm'])
        if args.discovery_source:
            discovery_source = args.discovery_source.read_bytes()
            require(json.loads(discovery_source) == json.loads(files['sites_logical.json']),
                    'Discovery source differs from the clean source')
            isomorphism.update(source_leaves_compared=5121,
                               discovery_source_sha256=b.sha(discovery_source),
                               clean_source_sha256=b.sha(files['sites_logical.json']))
        files['discovery_isomorphism.json'] = b.json_bytes(isomorphism)
    else:
        require(args.discovery_source is None, 'discovery-source requires discovery-table')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, data in files.items():
        (args.output_dir / name).write_bytes(data)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run without -O/-OO')
    main()
