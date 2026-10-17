"""Duplicate-permitting exact C254 term certificates, scratch research only.

The verifier has no constructor-key uniqueness test or node-interning index.
Every bundle gate carries a finite L/R distinguishing path. All templates and
all12 rule cases remain the attributed source50 ones. No TM cost is asserted.
"""
from pathlib import Path
import sys

# Read-only copied source50 dependencies, not the immutable intake extraction.
sys.path.insert(0, str(Path(__file__).resolve().parent / 'source50/code'))
import symbolic254 as S

FORMAT = 'term-c254-path-v1'


class Invalid(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Invalid(reason)


def validate_nodes(nodes, stats):
    """Single pass only. Duplicated positive keys are expressly allowed."""
    require(type(nodes) is list and bool(nodes) and nodes[0] == ['z'], 'zero_node')
    for i, node in enumerate(nodes[1:], 1):
        stats['node_records'] += 1
        require(type(node) is list and len(node) == 4 and node[0] == 'b', 'node_shape')
        _, tag, left, right = node
        require(type(tag) is int and 0 <= tag < 4, 'node_tag')
        require(all(type(j) is int and 0 <= j < i for j in (left, right)), 'node_reference')
        require((tag, left, right) != (0, 0, 0), 'zero_alias')
    # No set/dict of keys, pairwise node comparison, or interning operation here.


def terminal_mismatch(nodes, left, right):
    if left == 0 or right == 0:
        return (left == 0) != (right == 0)
    return nodes[left][1] != nodes[right][1]


def distinguish(nodes, left, right, path, stats=None):
    """Exact finite path: every bit descends equal nonzero tags; terminal differs.

    This routine assumes the local normal/topological arena checks already pass.
    It uses neither natural denotation nor a complete structural equality test.
    A mismatch before the path is exhausted is rejected as trailing witness data.
    """
    if stats is None:
        stats = {'path_edges': 0}
    if type(path) is not list or not all(type(b) is int and b in (0, 1) for b in path):
        return False
    for bit in path:
        if left == 0 or right == 0 or nodes[left][1] != nodes[right][1]:
            return False
        stats['path_edges'] += 1
        left = nodes[left][2 + bit]
        right = nodes[right][2 + bit]
    return terminal_mismatch(nodes, left, right)


class LookupArena:
    """Frozen deterministic first-match lookup; duplicates may cause rejection.

    apply is exactly the source50 fixed-template evaluator. Its small parameter
    environment dict is not an arena index. The only literal constants are0/1.
    """
    apply = S.Arena.apply

    def __init__(self, nodes, stats):
        self.nodes = nodes
        self.stats = stats

    def literal(self, value):
        if type(value) is int and value == 0:
            return 0
        if type(value) is int and value == 1:
            return self.b(1, 0, 0)
        raise Invalid('unexpected_template_literal')

    def b(self, tag, left, right):
        if tag == 0 and left == 0 and right == 0:
            return 0
        key = ['b', tag, left, right]
        for i in range(1, len(self.nodes)):
            self.stats['lookup_records'] += 1
            if self.nodes[i] == key:
                return i
        raise Invalid('missing_template_node')


def verify_certificate(cert, goal=None, *, stats=None):
    """FixedF by default. Trusted positive-control goal is outside the certificate."""
    if stats is None:
        stats = {}
    stats.update(node_records=0, lookup_records=0, path_edges=0, proof_rows=0,
                 arena_uniqueness_comparisons=0, reason=None)
    try:
        require(type(cert) is dict and cert.get('format') == FORMAT, 'format')
        nodes = cert['nodes']
        validate_nodes(nodes, stats)
        arena = LookupArena(nodes, stats)
        if goal is None:
            target = arena.b(1, 0, 0)
        else:
            require(type(goal) is int and 0 <= goal < len(nodes), 'control_goal')
            target = goal
        rows = cert['proof_rows']
        require(type(rows) is list, 'proof_list')
        formulas = []
        for i, row in enumerate(rows):
            stats['proof_rows'] += 1
            require(type(row) is dict, 'proof_row')
            tag, args, children = row['tag'], row['args'], row['children']
            require(type(tag) is int and 0 <= tag < 12, 'proof_tag')
            require(type(args) is list and len(args) == S.ARITY[tag], 'proof_arity')
            require(all(type(j) is int and 0 <= j < len(nodes) for j in args), 'argument')
            require(type(children) is list and len(children) ==
                    (2 if tag == 1 else 1 if tag == 2 else 0), 'premise_arity')
            require(all(type(j) is int and 0 <= j < i for j in children), 'premise_reference')
            if tag == 0:
                out = 0
            elif tag == 1:
                out = args[0]
                require(formulas[children[1]] == arena.apply(
                    'wim', [formulas[children[0]], out]), 'mp_major')
            elif tag == 2:
                out = arena.apply('wal', [args[0], formulas[children[0]]])
            elif tag == 11:
                paths = row['gate_paths']
                require(type(paths) is list and len(paths) == 2, 'gate_witness_arity')
                require(distinguish(nodes, args[2], args[0], paths[0], stats), 'bundle_gate_1')
                require(distinguish(nodes, args[2], args[1], paths[1], stats), 'bundle_gate_2')
                out = arena.apply('bundle', args)
            else:
                out = arena.apply('rho' + str(tag - 2), args)
            require(type(row['formula']) is int and row['formula'] == out, 'claimed_formula')
            formulas.append(out)
        require(bool(formulas) and formulas[-1] == target, 'fixed_or_control_endpoint')
        return True
    except (Invalid, ValueError, TypeError, KeyError, IndexError) as error:
        stats['reason'] = str(error)
        return False


# All code below is a certificate producer, never called by the verifier.
def find_path(nodes, left, right):
    """Find one distinguishing branch; None means equal unfolded normal trees."""
    pending = [(left, right, [])]
    visited = set()
    while pending:
        a, b, path = pending.pop()
        if (a, b) in visited:
            continue
        visited.add((a, b))
        if terminal_mismatch(nodes, a, b):
            return path
        if a == 0:  # both zero
            continue
        pending.append((nodes[a][3], nodes[b][3], path + [1]))
        pending.append((nodes[a][2], nodes[b][2], path + [0]))
    return None


def from_term(cert):
    """Producer: source50's interned cert remains complete for the new checker."""
    from copy import deepcopy
    out = deepcopy(cert)
    out['format'] = FORMAT
    for row in out['proof_rows']:
        if row['tag'] == 11:
            a, b, c = row['args']
            row['gate_paths'] = [find_path(out['nodes'], c, a),
                                 find_path(out['nodes'], c, b)]
            if any(p is None for p in row['gate_paths']):
                raise ValueError('Source gate terms have equal values')
    return out
