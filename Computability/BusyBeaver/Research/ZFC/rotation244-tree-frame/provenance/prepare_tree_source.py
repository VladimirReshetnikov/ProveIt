#!/usr/bin/env python3
"""Emit exact TreeRotation244 and audit; root alone invokes this source writer.

No compiler, checker, simulator, subprocess or dependency build is invoked.
Finite DAG expansion below only constructs and compares literal syntax trees.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROUTING_SHA = '060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b'
ROTATION_SHA = '3bb25d3b5068dadd3f217b11c3fa10be0a86a5df04e3b50073413d03e8daa20a'
AUDIT_SHA = 'cc7eed2b9dc83db9cbb3c4e911d0ddd01f40f8900c063dfb1e5ba02a33a73382'
SITES_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
PREFIX = 'SetTheory.BusyBeaver.ZFC.TreeRotation244.'
PROBES = ['tree_eq_fuel', 'tree_eq', 'walk_eq_tree', 'step_eq_tree',
          'leaf_count', 'node_count', 'depth_eq', 'halt_count']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def desc(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}


def edge_text(edge):
    kind, value = edge
    return '.halt' if kind == 'halt' else f'(.{kind} {value})'


def tree_edge(edge):
    return f't{edge[1]:03}' if edge[0] == 'node' else f'(.leaf {edge_text(edge)})'


def child_proof(edge):
    return (f'(fun f hf => node{edge[1]:03}_eq f hf)' if edge[0] == 'node'
            else '(fun _ _ => rfl)')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    assert not output.exists(), 'Use a fresh output directory.'
    assert not output.is_relative_to(repo), 'Scratch output must be outside the repository.'
    base = repo / 'Computability/BusyBeaver'
    routing = base / 'Lean/BusyBeaver/ZFC/ProgramRouting245.lean'
    rotation = base / 'Lean/BusyBeaver/ZFC/ProgramRotation244.lean'
    sites = base / 'Research/ZFC/candidate-rotation244/sites_logical.json'
    audit_template = Path(__file__).resolve().with_name('Audit-template.lean')
    for path, expected in [(routing, ROUTING_SHA), (rotation, ROTATION_SHA),
                           (sites, SITES_SHA), (audit_template, AUDIT_SHA)]:
        assert sha(path) == expected, (str(path), 'input changed')
    original = routing.read_text()
    matches = re.findall(r'^private def row(\d+) : Row := (.+)$', original, re.M)
    assert [int(index) for index, _ in matches] == list(range(203))
    rows = []
    for index_text, body in matches:
        tokens = re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?', body)
        assert len(tokens) == 2
        row = [(kind, int(value) if value else None) for kind, value in tokens]
        assert all(kind != 'node' or value < int(index_text) for kind, value in row)
        rows.append(row)
    assert rows[5] == [('decnz', 6), ('node', 4)]
    assert rows[6] == [('node', 5), ('inc', 0)]
    # These are the exact two branches in the pinned ProgramRotation244 source.
    rotated = rotation.read_text()
    assert 'if n = 5 then (.decnz 6, .cont 2)' in rotated
    assert 'else if n = 6 then (.inc 0, .node 5)' in rotated
    rows[5] = [('decnz', 6), ('cont', 2)]
    rows[6] = [('inc', 0), ('node', 5)]
    heights = []
    for row in rows:
        heights.append(1 + max(heights[value] if kind == 'node' else 0
                               for kind, value in row))
    leaves, reachable = [], set()
    names = {'inc': 'CI', 'decnz': 'CD', 'brk': 'CB', 'cont': 'CC', 'halt': 'CH'}

    def expand(edge, path):
        kind, value = edge
        if kind == 'node':
            reachable.add(value)
            expand(rows[value][0], path + '0')
            expand(rows[value][1], path + '1')
        else:
            leaves.append([path, names[kind], value])

    expand(('node', 202), '')
    assert leaves == json.loads(sites.read_text()), 'Complete ordered leaf certificate mismatch.'
    census = {'stored_rows': 203, 'reachable_rows': len(reachable),
              'leaves': len(leaves), 'internal_nodes': len(leaves) - 1,
              'depth': max(len(row[0]) for row in leaves),
              'halts': sum(row[1] == 'CH' for row in leaves)}
    assert census == dict(stored_rows=203, reachable_rows=202, leaves=6459,
                          internal_nodes=6458, depth=51, halts=1)
    assert set(range(203)) - reachable == {4}
    assert heights[202] == 51
    assert [row for row in leaves if row[0].startswith('011')] == [
        ['0110', 'CI', 0], ['01110', 'CD', 6], ['01111', 'CC', 2]]

    # Copy the already checked generic proof literally from its pinned source.
    helper = original.split('/-- Compose exact child unfoldings;', 1)[1]
    helper = '/-- Compose exact child unfoldings;' + helper.split('private def t000', 1)[0]
    assert helper.count('private theorem parent_eq') == 1
    header = '''import BusyBeaver.ZFC.ProgramRotation244

/-!
Exact complete source tree for the rotated 244 program. The 203 stored rows
unfold to 6,459 leaves and 6,458 internal nodes, at depth 51, with one halt.
Row 4 remains stored but is unreachable after the row 5/6 rotation.
All fuel, pointer, register and complete leaf-effect contracts below use the
actual ProgramRotation244.program. Binary coverage and simulation are separate.

The parent_eq proof pattern and program literals are adapted from the checked
ProgramRouting245 source. The original Mira-Cult machine/calculus, Jeff
Ketchersid calibration, Andrew James Wade register semantics, and prior
ProveIt routing work retain their attribution. The rotation is from source 71.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.TreeRotation244
open RegisterPath RMBisim ProgramRotation244

'''
    lines = [header, helper]
    for index, row in enumerate(rows):
        left, right = row
        hleft = heights[left[1]] if left[0] == 'node' else 0
        hright = heights[right[1]] if right[0] == 'node' else 0
        lines.extend([
            f'private def t{index:03} : Tree := .node {tree_edge(left)} {tree_edge(right)}\n',
            f'private theorem row{index:03}_eq : program.nodes {index} = '
            f'({edge_text(left)}, {edge_text(right)}) := by decide +kernel\n',
            f'private theorem node{index:03}_eq (f : Nat) (hf : {heights[index]} ≤ f) : '
            f'toTree program f {index} = t{index:03} := by\n',
            f'  exact parent_eq (h₀ := {hleft}) (h₁ := {hright}) row{index:03}_eq\n',
            f'    {child_proof(left)} {child_proof(right)} f hf\n\n'])
    suffix = original.split('/-- The exact complete certificate tree, with shared subterms only. -/', 1)[1]
    suffix = '/-- The exact complete certificate tree, with shared subterms only. -/' + suffix
    suffix = suffix.replace('leafCount tree = 6460', 'leafCount tree = 6459')
    suffix = suffix.replace('nodeCount tree = 6459', 'nodeCount tree = 6458')
    suffix = suffix.replace('end TreeRouting245\nend SetTheory.BusyBeaver.ZFC',
                            'end SetTheory.BusyBeaver.ZFC.TreeRotation244')
    assert suffix.endswith('end SetTheory.BusyBeaver.ZFC.TreeRotation244\n')
    lines.append(suffix)
    source = ''.join(lines)
    audit = audit_template.read_text()
    assert source.count('private theorem row') == source.count('private theorem node') == 203
    assert audit.count('#print axioms ') == 8 and len(re.findall(r'^example\b', audit, re.M)) == 10
    assert re.findall(r'^#print axioms (\S+)$', audit, re.M) == [PREFIX + p for p in PROBES]
    output.mkdir(parents=True)
    (output / 'TreeRotation244.lean').write_text(source)
    (output / 'Audit.lean').write_text(audit)
    literal_data = {'root': 202, 'rows': rows, 'heights': heights, 'census': census,
                    'unreachable_rows': [4], 'modified_rows': [5, 6],
                    'logical_sites': desc(sites), 'ordered_sites_equal': True}
    (output / 'tree-data.json').write_text(json.dumps(literal_data, indent=2) + '\n')
    inventory = {'status': 'GENERATED_NOT_BUILT', 'module': 'BusyBeaver.ZFC.TreeRotation244',
                 'generator': desc(__file__), 'inputs': [desc(p) for p in (routing, rotation, sites, audit_template)],
                 'source': desc(output / 'TreeRotation244.lean'), 'audit': desc(output / 'Audit.lean'),
                 'data': desc(output / 'tree-data.json'), 'direct_imports': ['BusyBeaver.ZFC.ProgramRotation244'],
                 'named_probes': [PREFIX + p for p in PROBES], 'typed_callers': 10,
                 'census': census, 'proof_commands': [], 'compiler_or_checker_invoked': False}
    (output / 'source-inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')
    print(json.dumps(desc(output / 'source-inventory.json')))


if __name__ == '__main__':
    main()
