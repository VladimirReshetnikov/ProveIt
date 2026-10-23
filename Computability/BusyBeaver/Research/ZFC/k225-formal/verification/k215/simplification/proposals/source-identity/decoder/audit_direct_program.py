#!/usr/bin/env python3
"""Owned read-only parser/audit. Never imports or executes upstream source."""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def bits(s):
    if not s.strip():
        return ()
    xs = tuple(x.strip() for x in s.split(','))
    assert all(x in ('false', 'true') for x in xs)
    return tuple(x == 'true' for x in xs)


def parse():
    provenance = json.loads((ROOT / 'source_provenance.json').read_text())
    for item in provenance['sources']:
        data = (ROOT / 'sources' / item['name']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == item['sha256']
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == item['github_blob_sha']
    source = (ROOT / 'sources' / 'K215Decoder.lean').read_text()
    node_text = source.split('def sourceNodes : Array Node := #[', 1)[1].split('\n]', 1)[0]
    nodes = []
    for line in node_text.splitlines():
        if line.strip():
            m = re.fullmatch(r'\s*\.(leaf|fork) (\d+) (\d+),?', line)
            assert m, line
            nodes.append((m[1], int(m[2]), int(m[3])))
    program_text = (ROOT / 'sources' / 'KSource215Program.lean').read_text()
    pnodes = []
    for line in program_text.split('def p215Nodes', 1)[1].split('def p215 :', 1)[0].splitlines():
        m = re.fullmatch(r'\s*\| (\d+) => (.*)', line)
        if m:
            assert int(m[1]) == len(pnodes)
            es = re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?', m[2])
            assert len(es) == 2
            pnodes.append(tuple((op, int(arg) if arg else 0) for op, arg in es))
    pmeta = re.search(r'def p215 : Program := ⟨p215Nodes, (\d+), (\d+)⟩', program_text)
    root, nnodes = map(int, pmeta.groups())
    blocks = []
    for q, q2, word, steps in re.findall(r'⟨(\d+), (\d+), \[([^\]]*)\], (\d+)⟩', source.split('def blocks', 1)[1].split('def roles', 1)[0]):
        blocks.append((int(q), int(q2), bits(word), int(steps)))
    roles = []
    for line in source.split('def roles : Array Role := #[', 1)[1].split('\n]', 1)[0].splitlines():
        if not line.strip():
            continue
        m = re.fullmatch(r'\s*⟨(\d+), (\d+), \[([^\]]*)\], (.*)⟩,?', line)
        assert m, line
        edges = []
        pattern = r'\(\.(internal) (\d+) (\d+)\)|\(\.(primitive) (\d+) ⟨(false|true), (1|\(-1\)), (\d+)⟩\)'
        for x in re.finditer(pattern, m[4]):
            if x[1]:
                edges.append(('internal', int(x[2]), int(x[3])))
            else:
                edges.append(('primitive', int(x[5]), (x[6] == 'true', 1 if x[7] == '1' else -1, int(x[8]))))
        assert len(edges) == 2
        roles.append((int(m[1]), int(m[2]), bits(m[3]), *edges))
    return provenance, nodes, pnodes, root, nnodes, blocks, roles


def audit():
    provenance, nodes, pnodes, root, nnodes, blocks, roles = parse()
    forks = [i for i, x in enumerate(nodes) if x[0] == 'fork']
    node_map = {old: new for new, old in enumerate(forks)}
    primitive = {0: 'inc', 1: 'decnz', 2: 'brk', 3: 'cont', 4: 'halt'}

    def image(n):
        op, a, b = nodes[n]
        if op == 'fork':
            return ('node', node_map[n])
        assert a in primitive
        return (primitive[a], b)

    def program_agrees(ps, mp):
        def img(n):
            if nodes[n][0] == 'fork':
                return ('node', mp[n])
            return image(n)
        return len(ps) == len(mp) and all(ps[mp[i]] == (img(nodes[i][1]), img(nodes[i][2])) for i in mp)

    assert len(nodes) == 202 and len(forks) == nnodes == len(pnodes) == 179
    assert node_map[201] == root == 178
    assert program_agrees(pnodes, node_map)
    assert all(child < i for i, (tag, l, r) in enumerate(nodes) if tag == 'fork' for child in (l, r))
    assert all(k < j for j, es in enumerate(pnodes) for tag, k in es if tag == 'node')
    direct_roles = [(node_map[n], q, suffix, zero, one) for n, q, suffix, zero, one in roles]
    assert len(set((n, suffix) for n, q, suffix, *_ in direct_roles)) == len(roles) == 234
    edge_records = []
    for rid, (n, q, suffix, zero, one) in enumerate(roles):
        assert 0 < len(suffix) <= 2 and nodes[n][0] == 'fork'
        for bit, edge in enumerate((zero, one)):
            child = nodes[n][1 + bit]
            expected = pnodes[node_map[n]][bit]
            assert expected == image(child)
            if edge[0] == 'internal':
                _, k, j = edge
                sn, sq, ss, *_ = roles[k]
                entry, exit_, word, steps = blocks[j]
                w = suffix + (bool(bit),)
                assert nodes[child][0] == 'fork'
                assert sn == child and ss == w[-2:]
                assert entry == q and exit_ == sq and len(word) <= len(w)
                assert word == w[-len(word):] and 1 <= steps <= 7
                assert expected == ('node', direct_roles[k][0])
            else:
                assert nodes[child][0] == 'leaf' and edge[1] == child
                assert expected[0] != 'node'
            edge_records.append({'role': rid, 'bit': bool(bit), 'old_child': child,
                                 'program_edge': list(expected), 'kind': edge[0]})

    leaves = []
    def expand(n, path):
        tag, a, b = nodes[n]
        if tag == 'leaf':
            leaves.append((path, image(n)))
        else:
            expand(a, path + (False,))
            expand(b, path + (True,))
    expand(201, ())
    def walk(P):
        n = root
        for i in range(nnodes + 1):
            edge = pnodes[n][int(P[i]) if i < len(P) else 0]
            if edge[0] != 'node':
                return edge, i + 1
            n = edge[1]
        return None
    for word, edge in leaves:
        assert walk(word) == (edge, len(word))
        # Successful decoding ignores arbitrary appended unread bits.
        for suffix in ((), (False,), (True,), (True, False, True)):
            assert walk(word + suffix) == (edge, len(word))
        # Erasing the final zero run exercises implicit zero extension.
        trimmed = word
        while trimmed and not trimmed[-1]:
            trimmed = trimmed[:-1]
        assert walk(trimmed) == (edge, len(word))

    bad_map = dict(node_map)
    bad_map[2], bad_map[7] = bad_map[7], bad_map[2]
    bad_program = list(pnodes)
    bad_program[0] = (('inc', 8), pnodes[0][1])
    bad_child = list(pnodes)
    bad_child[root] = (('node', root), pnodes[root][1])
    assert not program_agrees(pnodes, bad_map)
    assert not program_agrees(bad_program, node_map)
    assert not program_agrees(bad_child, node_map)
    result = {
        'pin': provenance['pin'], 'status': 'finite source-data audit only; not Lean or Rocq compilation',
        'alternate_nodes': len(nodes), 'forks': len(forks), 'primitive_nodes': len(nodes) - len(forks),
        'literal_program_nodes': nnodes, 'old_root': 201, 'direct_root': root,
        'roles': len(roles), 'blocks': len(blocks),
        'checked_role_branches': len(edge_records),
        'role_branch_kinds': dict(Counter(x['kind'] for x in edge_records)),
        'expanded_leaves': len(leaves),
        'expanded_guarded_outcomes': sum(2 if e[0] == 'decnz' else 1 for _, e in leaves),
        'leaf_depth_min': min(len(w) for w, _ in leaves),
        'leaf_depth_max': max(len(w) for w, _ in leaves),
        'leaf_opcode_counts': dict(Counter(e[0] for _, e in leaves)),
        'checks': {'all_179_local_squares': True, 'all_468_retargeted_branches': True,
                   'role_node_suffix_keys_unique': True, 'source_child_labels_decrease': True,
                   'full_leaf_walks': True, 'appended_unread_bits': True,
                   'trailing_zero_erasure': True},
        'negative_controls': {'swapped_fork_labels_rejected': True,
                              'changed_primitive_rejected': True,
                              'changed_root_child_rejected': True},
        'not_checked': ['universal decoder semantics', 'physical table rows', 'block execution',
                        'Lean typechecking', 'Rocq typechecking', 'endpoint integration', 'performance'],
    }
    mapping = {'pin': provenance['pin'], 'rule': 'The j-th fork in sourceNodes has p215 node label j.',
               'fork_map': [{'decoder_node': n, 'program_node': j} for n, j in node_map.items()],
               'primitive_map': [{'decoder_node': i, 'program_edge': list(image(i))}
                                 for i, x in enumerate(nodes) if x[0] == 'leaf'],
               'retargeted_roles': [{'role': i, 'old_node': old[0], 'program_node': new[0],
                                     'physical_state': old[1], 'suffix': list(old[2])}
                                    for i, (old, new) in enumerate(zip(roles, direct_roles))],
               'branch_bindings': edge_records}
    return result, mapping


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    result, mapping = audit()
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        (args.output_dir / 'DIRECT_PROGRAM_AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
        (args.output_dir / 'NODE_AND_ROLE_MAP.json').write_text(json.dumps(mapping, indent=2) + '\n')
    print(json.dumps(result, indent=2))
