#!/usr/bin/env python3
"""Reconstruct the proposed source tree from pinned PA196/Program.lean.

Usage: python reconstruct_halt_at_mp.py --program PA196/Program.lean --output DIR

No Lean toolchain or third-party Python module is used.  The parser deliberately
accepts only the tiny literal Tree-definition fragment used by the pinned file.
It does not parse Lean proofs or establish any new kernel-checked theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from halt_at_mp_source_checks import resolve

HERE = Path(__file__).resolve().parent

PROGRAM_SHA256 = '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
EXPECTED_SITES_SHA256 = '9b3886a936eb72baa609413c3579c1808c2f3af81468d4260eae680c0dc2d468'


def parse_program(raw):
    definitions = {}
    operations = {'.inc': 'CI', '.dec': 'CD', '.breakTo': 'CB',
                  '.continueTo': 'CC', '.halt': 'CH'}

    def expression(tokens):
        token = tokens.pop(0)
        if token == '(':
            result = expression(tokens)
            assert tokens.pop(0) == ')'
            return result
        if token == '.node':
            return expression(tokens), expression(tokens)
        if token == '.leaf':
            return expression(tokens)
        if token in operations:
            return operations[token], None if token == '.halt' else int(tokens.pop(0))
        assert token in definitions, token
        return definitions[token]

    for line in raw.decode().splitlines():
        match = re.fullmatch(r'def ((?:node|x)\d+) : Tree := (.+)', line)
        if match:
            tokens = re.findall(r'\(|\)|\.[A-Za-z]+|(?:node|x)\d+|\d+', match[2])
            definitions[match[1]] = expression(tokens)
            assert not tokens
    assert len(definitions) == 159
    return definitions


def is_leaf(tree):
    return isinstance(tree[0], str)


def sites(tree, path=''):
    if is_leaf(tree):
        return [[path, *tree]]
    return sites(tree[0], path + '0') + sites(tree[1], path + '1')


def count_internal(tree):
    found = set()

    def visit(node):
        if is_leaf(node) or node in found:
            return
        found.add(node)
        visit(node[0])
        visit(node[1])

    visit(tree)
    return len(found)


def main():
    if not __debug__:
        raise RuntimeError('Run without Python -O or -OO; assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--program', type=Path,
                        default=HERE.parent / 'rotated196/upstream/PA196/Program.lean')
    parser.add_argument('--output', type=Path,
                        default=HERE / 'reconstructed_source')
    args = parser.parse_args()
    raw = args.program.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == PROGRAM_SHA256, ('different upstream Program.lean', digest)
    n = parse_program(raw)
    old = n['node172']

    # Only these command-local pieces change.  In particular, the complete
    # generated AX subtree node161 is reused literally.
    success = ((n['node51'], n['node19']), (('CI', 6), n['node7']))
    mp = (n['node162'], (n['node6'], success))
    ax_or_mp = (n['node161'], mp)
    command_body = (ax_or_mp, ('CC', 3))
    dispatch = (('CD', 3), command_body)
    total_shift = (n['node145'], (('CD', 5), n['node38']))
    cycle = (n['node36'], (dispatch, total_shift))
    new = (n['node20'], (cycle, ('CC', 2)))
    old_rows, new_rows = sites(old), sites(new)
    assert len(old_rows) == 3812 and len(new_rows) == 3788
    assert count_internal(old) == 159 and count_internal(new) == 162
    # All reused instructions, including their complete outgoing control
    # edges, agree under this finite map.  It covers the entire original
    # AX command, fetch machinery, MP prelude, and root stack decoder.
    old_graph, new_graph = resolve(old_rows), resolve(new_rows)
    relocate = {i: i - 11 for i in range(11, 3773)}
    relocate.update({3773: 3762, 3799: 3781, 3800: 3782})
    for i in range(11, 3773):
        instruction = old_graph[i]
        if instruction[0] in ('inc', 'dec'):
            translated = (*instruction[:2], *(relocate[j] for j in instruction[2:]))
        else:
            translated = (instruction[0], *(relocate[j] for j in instruction[1:]))
        assert translated == new_graph[relocate[i]], (i, instruction, translated)
    # Root's source construction uses the canonical compact JSON format.
    encoded = (json.dumps(new_rows, separators=(',', ':')) + '\n').encode()
    candidate_digest = hashlib.sha256(encoded).hexdigest()
    assert candidate_digest == EXPECTED_SITES_SHA256, candidate_digest
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'sites.json').write_bytes(encoded)
    result = {
        'upstream_commit': '407cdc356f6b586635e71ac92be394255f4bfea4',
        'upstream_program_sha256': digest,
        'candidate_sites_sha256': candidate_digest,
        'old_leaf_sites': len(old_rows),
        'new_leaf_sites': len(new_rows),
        'old_internal_dag_nodes': count_internal(old),
        'new_internal_dag_nodes': count_internal(new),
        'reused_sites_with_all_cfg_edges_checked': 3762,
        'scope': 'Literal source reconstruction; no binary TM count is claimed.',
    }
    (args.output / 'reconstruction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
