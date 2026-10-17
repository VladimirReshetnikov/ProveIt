#!/usr/bin/env python3
"""Generate complete structural decoder coverage for permutation252 site checks.

Untrusted program parsing chooses a bounded cut frontier. Each subtree check
is a closed Lean kernel decision, and allSites_join composes BOTH children
against the actual shared tree. A path list or an external coverage assertion
is never supplied as a proof premise. Pilot output deliberately omits the
full-coverage theorem and requires a separate output file.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import bisim254

REPO = Path(__file__).resolve().parents[4]
TARGET = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SitesPerm252.lean'


class Tree:
    def __init__(self, edge=None, left=None, right=None):
        self.edge, self.left, self.right = edge, left, right
        if edge is not None:
            self.nodes, self.leaves, self.guards, self.depth = 0, 1, 2 if edge[0] == 'decnz' else 1, 0
        else:
            assert left is not None and right is not None
            self.nodes = 1 + left.nodes + right.nodes
            self.leaves = left.leaves + right.leaves
            self.guards = left.guards + right.guards
            self.depth = 1 + max(left.depth, right.depth)


def unfold(rows, n=0, ancestors=frozenset()):
    assert n not in ancestors and 0 <= n < len(rows)
    def child(e):
        return unfold(rows, e[1], ancestors | {n}) if e[0] == 'node' else Tree(edge=e)
    return Tree(left=child(rows[n][0]), right=child(rows[n][1]))


def bits(path):
    return '[' + ', '.join('true' if b else 'false' for b in path) + ']'


def emit(max_guards, pilot_blocks=0):
    tree = unfold(bisim254.load_prog254())
    assert (tree.nodes, tree.leaves, tree.guards, tree.depth) == (6459, 6460, 8391, 34)
    chunks = []

    def split(t, path):
        if t.guards <= max_guards:
            i = len(chunks)
            chunks.append({'index': i, 'path': path, 'path_length': len(path),
                           'leaves': t.leaves, 'guards': t.guards, 'subtree_depth': t.depth})
            return f'block_{i}'
        assert t.edge is None
        a, b = split(t.left, path + [False]), split(t.right, path + [True])
        return (f'(allSites_join SitePerm252.checkSite {bits(path[::-1])}\n'
                f'  (descend ActualTree254.tree {bits(path + [False])})\n'
                f'  (descend ActualTree254.tree {bits(path + [True])})\n'
                f'  {a} {b})')

    complete_proof = split(tree, [])
    assert sum(c['leaves'] for c in chunks) == 6460
    assert sum(c['guards'] for c in chunks) == 8391
    selected = chunks[:pilot_blocks] if pilot_blocks else chunks
    assert not pilot_blocks or pilot_blocks <= len(chunks)
    out = ['''import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePerm252

/-!
Generated closed checks for the complete literal Prog254 decoder tree.
Every chunk has a bounded number of zero/positive guard cases. The final
proof composes both children at every cut against the actual tree itself.
No external coverage premise or register-operation oracle is assumed.
This layer establishes per-site coverage, not the dispatch invariant or a
standard-ZFC consistency endpoint. Generator: generate_sites_perm252.py.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPerm252
open RegisterPath RMBisim SiteCoverage
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem node_count : nodeCount ActualTree254.tree = 6459 := by decide +kernel
theorem leaf_count : leafCount ActualTree254.tree = 6460 := by decide +kernel
theorem guard_count : guardCount ActualTree254.tree = 8391 := by decide +kernel
theorem decoder_depth : depth ActualTree254.tree = 34 := by decide +kernel
''']
    for c in selected:
        p = c['path']
        out.append(f'''/-- Chunk {c['index']}: {c['leaves']} leaves, {c['guards']} guard cases. -/
private theorem block_{c['index']} :
    allSites SitePerm252.checkSite {bits(p[::-1])}
      (descend ActualTree254.tree {bits(p)}) = true := by decide +kernel
''')
    if pilot_blocks:
        out.append(f'-- PILOT ONLY: {len(selected)} of {len(chunks)} chunks; no all-sites theorem.\n')
    else:
        out.append('''/-- Structural composition covers every leaf of the actual decoder. -/
theorem all_sites : allSites SitePerm252.checkSite [] ActualTree254.tree = true :=
'''+complete_proof+'''

/-- Every successful actual walk receives its exact checked consumed path. -/
theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e, d)) :
    SitePerm252.checkSite (consume P d) e = true :=
  allSites_walk SitePerm252.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P e d hw

/-- The complete finite decoder also supplies walk existence for arbitrary PCs. -/
theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e, d) :=
  allSites_walk_total SitePerm252.checkSite Prog254.program ActualTree254.tree
    ActualTree254.tree_eq all_sites P
''')
    out.append('end SetTheory.BusyBeaver.ZFC.SitesPerm252\n')
    data = '\n'.join(out).encode('utf-8')
    report = {'scope': 'Generated source only until kernel checked; complete binary cut composition, no external coverage axiom.',
              'max_guards_per_chunk': max_guards, 'chunks': len(chunks), 'selected_chunks': len(selected),
              'pilot_only': bool(pilot_blocks), 'nodes': tree.nodes, 'leaves': tree.leaves,
              'guard_cases': tree.guards, 'decoder_depth': tree.depth,
              'chunk_guard_histogram': dict(sorted(Counter(c['guards'] for c in chunks).items())),
              'cut_frontier': chunks, 'source_bytes': len(data), 'source_sha256': hashlib.sha256(data).hexdigest()}
    return data, report


def emit_batches(max_guards, output, batches=8):
    """Persist the same closed checks in independently checked modules.

    Only theorem visibility and module boundaries change. In particular the
    actual allSites/checkSite arguments and the final cut composition remain
    byte-exact to the original monolithic generator.
    """
    monolithic, report = emit(max_guards)
    original = monolithic.decode('utf-8')
    first = original.index('/-- Chunk 0:')
    final = original.index('/-- Structural composition')
    body = original[first:final]
    blocks = re.findall(r'/-- Chunk \d+:.*?private theorem block_\d+.*?by decide \+kernel\n',
                        body, re.S)
    assert len(blocks) == report['chunks']
    assert ''.join(blocks).replace('\n', '') == body.replace('\n', '')
    assert [int(re.search(r'theorem block_(\d+)', s)[1]) for s in blocks] == list(range(len(blocks)))
    prefix = '''import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePerm252

/-!
Generated persisted batch of the exact permutation252 closed site checks.
All check expressions are unchanged from the original complete cut frontier.
The final SitesPerm252 module imports all batches and composes both children
at every cut against ActualTree254.tree. No external coverage premise is used.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPerm252
open RegisterPath RMBisim SiteCoverage
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

'''
    files, parts = {}, []
    for i in range(batches):
        start, stop = i * len(blocks) // batches, (i + 1) * len(blocks) // batches
        name = f'SitesPerm252Checks{i}'
        selected = [s.replace('private theorem block_', 'theorem block_', 1)
                    for s in blocks[start:stop]]
        text = prefix + '\n'.join(selected) + '\nend SetTheory.BusyBeaver.ZFC.SitesPerm252\n'
        data = text.encode('utf-8')
        files[output.parent / (name + '.lean')] = data
        parts.append({'module': name, 'start_chunk': start, 'stop_chunk_exclusive': stop,
                      'chunks': stop - start,
                      'guards': sum(c['guards'] for c in report['cut_frontier'][start:stop]),
                      'source_bytes': len(data), 'source_sha256': hashlib.sha256(data).hexdigest()})
    imports = ''.join(f'import BusyBeaver.ZFC.{p["module"]}\n' for p in parts)
    result = (imports + original[:first] + original[final:]).encode('utf-8')
    files[output] = result
    report.update({'scope': 'Generated persisted batches only until each module and final composition is kernel checked.',
                   'monolithic_source_sha256': hashlib.sha256(monolithic).hexdigest(),
                   'check_expressions_unchanged': True, 'final_composition_unchanged': True,
                   'persisted_batches': parts, 'source_bytes': len(result),
                   'source_sha256': hashlib.sha256(result).hexdigest()})
    return files, report


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--out', type=Path, default=TARGET)
    p.add_argument('--metadata', type=Path)
    p.add_argument('--max-guards', type=int, default=64)
    p.add_argument('--pilot-blocks', type=int, default=0)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    if not __debug__:
        p.error('Assertions must remain enabled')
    if not 2 <= a.max_guards <= 256 or a.pilot_blocks < 0:
        p.error('Invalid bounded chunk parameters')
    if a.pilot_blocks and a.out.resolve() == TARGET.resolve():
        p.error('Pilot requires a separate output file')
    if a.pilot_blocks:
        data, report = emit(a.max_guards, a.pilot_blocks)
        files = {a.out: data}
    else:
        files, report = emit_batches(a.max_guards, a.out)
    for path, data in files.items():
        if a.check:
            if path.read_bytes() != data:
                p.error(f'Generated site coverage source differs: {path}')
        else:
            path.write_bytes(data)
    if a.metadata:
        a.metadata.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('chunks', 'selected_chunks', 'pilot_only', 'leaves', 'guard_cases', 'source_bytes')}, indent=2))


if __name__ == '__main__':
    main()
