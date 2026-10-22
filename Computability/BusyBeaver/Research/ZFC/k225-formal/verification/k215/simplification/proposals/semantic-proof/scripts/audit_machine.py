#!/usr/bin/env python3
"""Read-only census of K215 source leaves and routed primitive families.

This is an independent static census, not a Lean/Rocq proof checker. It accepts
an explicit repository path and writes JSON only when --output is supplied.
The parser fails on unrecognized current data syntax rather than guessing.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re
import subprocess


def census(repo: Path) -> dict:
    rel = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/K215Decoder.lean')
    path = repo / rel
    raw = path.read_bytes()
    text = raw.decode('utf-8')
    node_text = text.split('def sourceNodes : Array Node := #[', 1)[1].split('\n]', 1)[0]
    nodes = []
    for line in node_text.splitlines():
        line = line.strip()
        if not line:
            continue
        match = re.fullmatch(r'\.(leaf|fork) (\d+) (\d+),?', line)
        if match is None:
            raise ValueError(f'Unrecognized source node: {line!r}')
        nodes.append((match[1], int(match[2]), int(match[3])))
    role_text = text.split('def roles : Array Role := #[', 1)[1].split('\n]', 1)[0]
    roles = []
    for line in role_text.splitlines():
        line = line.strip()
        if not line:
            continue
        match = re.fullmatch(r'⟨(\d+), (\d+), \[([^]]+)\], (.*)⟩,?', line)
        if match is None:
            raise ValueError(f'Unrecognized role: {line!r}')
        edges = list(re.finditer(r'\.(internal|primitive) (\d+) (\d+|⟨[^⟩]+⟩)', match[4]))
        if len(edges) != 2:
            raise ValueError(f'Role does not have two parsed edges: {line!r}')
        roles.append((int(match[1]), int(match[2]), match[3],
                      [(e[1], int(e[2]), e[3]) for e in edges]))
    root_match = re.search(r'^def sourceRoot : Nat := (\d+)$', text, re.M)
    if root_match is None:
        raise ValueError('Source root not found')
    root = int(root_match[1])
    primitive_edges = []
    for rid, role in enumerate(roles):
        for bit, edge in enumerate(role[3]):
            if edge[0] == 'primitive':
                leaf = nodes[edge[1]]
                if leaf[0] != 'leaf':
                    raise ValueError('Primitive edge does not target a source leaf')
                primitive_edges.append((rid, bit, edge[1], leaf[1], leaf[2]))
    leaves = []
    def walk(node: int, prefix: str) -> None:
        kind, a, b = nodes[node]
        if kind == 'leaf':
            leaves.append((prefix, a, b))
        else:
            if not (a < node and b < node):
                raise ValueError('Source is not a downward-indexed DAG')
            walk(a, prefix + '0')
            walk(b, prefix + '1')
    walk(root, '')
    role_ops = collections.Counter(p[3] for p in primitive_edges)
    leaf_ops = collections.Counter(op for _, op, _ in leaves)
    op_names = {0: 'increment', 1: 'decrement_or_zero', 2: 'break', 3: 'continue', 4: 'halt'}
    operation_rows = []
    for op in sorted(set(role_ops) | set(leaf_ops)):
        mult = 2 if op == 1 else 1
        operation_rows.append({
            'op': op_names.get(op, str(op)),
            'source_occurrences': leaf_ops[op],
            'source_outcomes': mult * leaf_ops[op],
            'role_entries': role_ops[op],
            'role_outcomes': mult * role_ops[op],
        })
    return {
        'status': 'STATIC_CENSUS_ONLY',
        'commit': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
        'input': str(rel), 'input_sha256': hashlib.sha256(raw).hexdigest(),
        'source_nodes': len(nodes), 'roles': len(roles), 'source_leaves': len(leaves),
        'source_outcomes': len(leaves) + leaf_ops[1],
        'primitive_role_entries': len(primitive_edges),
        'primitive_role_outcomes': len(primitive_edges) + role_ops[1],
        'max_consumed_word_length': max(len(prefix) for prefix, _, _ in leaves),
        'operations': operation_rows,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository', type=Path)
    ap.add_argument('--output', type=Path)
    ns = ap.parse_args()
    data = json.dumps(census(ns.repository), indent=2) + '\n'
    if ns.output:
        ns.output.write_text(data)
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
