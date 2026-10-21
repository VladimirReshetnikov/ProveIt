#!/usr/bin/env python3
"""Hash-cons K215's two expanded Tree values without changing its certificate.

Usage:
  python3 share_trees.py --input reference/KSource215Data.lean --out pilot \
      --lean /path/to/lean

The default input is the preserved file at ProveIt commit
b6c7087477e51c017003bd729e712c8969733223.  This script is untrusted;
all executable certificate entries and existing theorem statements are retained.
It additionally emits a standalone Lean proof that each shared constructor tree
is definitionally equal to its original literal tree.  That small audit is not
a rebuild of the full ProveIt endpoint or its 185-module dependency closure.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PATTERN = re.compile(r'^def (t215|tD) : Tree :=\n[ \t]*([^\n]*)', re.MULTILINE)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse(text: str):
    tokens = re.findall(r'\(|\)|[^()\s]+', text)
    pos = 0
    def expr():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token != '(':
            return token
        items = []
        while tokens[pos] != ')':
            items.append(expr())
        pos += 1
        return tuple(items)
    result = expr()
    assert pos == len(tokens), 'Trailing tokens'
    return result


def tree_stats(expr):
    if expr[0] == '.leaf':
        return 1, 1
    assert expr[0] == '.node' and len(expr) == 3
    ln, ld = tree_stats(expr[1])
    rn, rd = tree_stats(expr[2])
    return ln + rn, 1 + max(ld, rd)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    ap.add_argument('--input', type=Path, default=here / 'reference/KSource215Data.lean')
    ap.add_argument('--out', type=Path, default=here / 'pilot')
    ap.add_argument('--lean', type=Path)
    args = ap.parse_args()
    source_bytes = args.input.read_bytes()
    source = source_bytes.decode('utf-8')
    matches = list(PATTERN.finditer(source))
    assert [m[1] for m in matches] == ['t215', 'tD'], 'Unexpected source layout'
    nodes = []
    index = {}
    originals = {}
    roots = {}
    per_tree = {}

    def intern(expr):
        if expr[0] == '.leaf':
            assert len(expr) == 2
            atom = expr[1]
            if isinstance(atom, str):
                assert atom == '.halt'
                op = atom
            else:
                assert len(atom) == 2 and atom[0] in ('.inc', '.decnz', '.cont', '.brk')
                assert atom[1].isdigit()
                op = ' '.join(atom)
            key = ('leaf', op)
        else:
            assert expr[0] == '.node' and len(expr) == 3
            key = ('node', intern(expr[1]), intern(expr[2]))
        if key not in index:
            index[key] = len(nodes)
            nodes.append(key)
        return index[key]

    def expand(i):
        node = nodes[i]
        if node[0] == 'leaf':
            tokens = node[1].split()
            return ('.leaf', tokens[0] if len(tokens) == 1 else tuple(tokens))
        return ('.node', expand(node[1]), expand(node[2]))

    def reachable(i, seen):
        if i in seen:
            return
        seen.add(i)
        if nodes[i][0] == 'node':
            reachable(nodes[i][1], seen)
            reachable(nodes[i][2], seen)

    for m in matches:
        originals[m[1]] = m[2]
        expr = parse(m[2])
        roots[m[1]] = intern(expr)
        assert expand(roots[m[1]]) == expr, 'Exact constructor-tree equality failed'
        leaves, height = tree_stats(expr)
        seen = set()
        reachable(roots[m[1]], seen)
        per_tree[m[1]] = dict(leaves=leaves, constructor_height=height,
                             unique_nodes=len(seen), root=roots[m[1]],
                             original_definition_bytes=len(m[0].encode('utf-8')))

    def render_node(i, node):
        body = (f'.leaf ({node[1]})' if node[0] == 'leaf'
                else f'.node sharedTree{node[1]} sharedTree{node[2]}')
        return f'private def sharedTree{i} : Tree := {body}'

    shared = '\n'.join(render_node(i, node) for i, node in enumerate(nodes)) + '\n\n'
    rewritten = PATTERN.sub(lambda m: f'def {m[1]} : Tree := sharedTree{roots[m[1]]}', source)
    insertion = rewritten.index('def t215 : Tree :=')
    rewritten = rewritten[:insertion] + shared + rewritten[insertion:]
    # This restoration check compares every byte outside the two tree definitions.
    restored = rewritten.replace(shared, '', 1)
    for m in matches:
        restored = restored.replace(f'def {m[1]} : Tree := sharedTree{roots[m[1]]}', m[0], 1)
    assert restored == source, 'An unrelated source byte changed'

    args.out.mkdir(parents=True, exist_ok=True)
    output = args.out / 'KSource215Data.lean'
    output.write_text(rewritten, encoding='utf-8')
    audit = '''import Init

/-! Standalone data equality only. This does not import the ProveIt endpoint. -/
namespace SharedTreeAudit
inductive Op where
  | inc (r : Nat)
  | decnz (r : Nat)
  | cont (k : Nat)
  | brk (k : Nat)
  | halt
inductive Tree where
  | leaf (op : Op)
  | node (left right : Tree)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

'''
    audit += shared
    for name in ('t215', 'tD'):
        audit += f'def original_{name} : Tree :=\n  {originals[name]}\n\n'
        audit += f'def compact_{name} : Tree := sharedTree{roots[name]}\n\n'
        audit += (f'theorem exact_{name} : compact_{name} = original_{name} := by rfl\n'
                  f'#print axioms exact_{name}\n\n')
    audit += 'end SharedTreeAudit\n'
    audit_path = args.out / 'SharedTreesAudit.lean'
    audit_path.write_text(audit, encoding='utf-8')

    result = {
        'schema': 'k215-data-sharing-v1',
        'snapshot': 'b6c7087477e51c017003bd729e712c8969733223',
        'source': 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean',
        'before_bytes': len(source_bytes),
        'after_bytes': len(rewritten.encode('utf-8')),
        'saved_bytes': len(source_bytes) - len(rewritten.encode('utf-8')),
        'source_sha256': sha(source_bytes),
        'output_sha256': sha(rewritten.encode('utf-8')),
        'joint_unique_nodes': len(nodes),
        'trees': per_tree,
        'exact_constructor_reconstruction': True,
        'all_other_bytes_preserved': True,
        'certificate_entries_changed': 0,
        'full_endpoint_rebuilt': False,
        'standalone_kernel_check': {'status': 'not_requested'}
    }
    if args.lean:
        proc = subprocess.run([str(args.lean), str(audit_path.resolve())],
                              capture_output=True, text=True)
        (args.out / 'shared_tree_kernel.log').write_text(proc.stdout + proc.stderr)
        version = subprocess.check_output([str(args.lean), '--version'], text=True).strip()
        result['standalone_kernel_check'] = {
            'status': 'PASS' if proc.returncode == 0 else 'FAIL',
            'returncode': proc.returncode,
            'version': version,
            'stdout': proc.stdout,
            'stderr': proc.stderr,
            'audit_sha256': sha(audit_path.read_bytes()),
            'scope': 'Definitional equality in a freely generated two-constructor Tree type'
        }
        assert proc.returncode == 0, proc.stdout + proc.stderr
    (args.out / 'sharing_receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
