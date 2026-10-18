#!/usr/bin/env python3
"""Bind the audited cache-MP decoder to exactly one source-DAG edge edit.

Standard library only. Exact source hashes are checked before parsing.
Full ordered tree comparison establishes that the decoder JSON is the literal
Prog254.v tree with only prefix111111 replaced by Dag254 helper197.

The 219-node source and literal tree are intentionally not compared by
unrestricted associativity. A complete segment bisimulation relates all
register-test sites: both branches have the same increment counts before
the next paired test. This is precisely the ordinary proof interface of
ProveIt's retained RMBisim.Bisim.halts_iff theorem. No Lean build is claimed.
"""
import argparse
from collections import Counter, deque
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

PIN = '43026ff42f0939f09b9e95495248cfadcad38e38'
PROG_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
DAG_SHA = '538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3'
DECODER_SHA = '04b5d434b135ed2a464f9409bc3fd34f0ffa4f836b9b126c97b388747b077a8c'
REWRITE_PATH = '111111'
SEGMENT_FUEL = 1000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_pinned(path, expected):
    raw = path.read_bytes()
    require(sha(raw) == expected, f'source SHA-256 mismatch: {path.name}')
    return raw.decode('utf-8')


def parse_prog(text):
    body = text.split('Definition p254_tab : list (cedge * cedge) := [', 1)[1].split('].', 1)[0]
    def edge(s):
        words = s.split()
        return (words[0][1:], int(words[1])) if len(words) == 2 else ('H',)
    rows = re.findall(r'\((C\w+(?: [0-9]+)?), (C\w+(?: [0-9]+)?)\)', body)
    nodes = {i: (edge(a), edge(b)) for i, (a, b) in enumerate(rows)}
    require(len(nodes) == 6459, 'wrong literal Prog254 node count')
    require(re.search(r'root\s*:=\s*0\s*;', text) is not None, 'wrong literal source root')
    return nodes


def parse_dag(text):
    names = {'ENode': 'N', 'EInc': 'I', 'EDecnz': 'D',
             'EBreak': 'B', 'EContinue': 'C', 'EHalt': 'H'}
    def edge(s):
        words = s.split()
        return (names[words[0]], int(words[1])) if len(words) == 2 else ('H',)
    rows = re.findall(r'\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)', text)
    require(len(rows) == 219 and len({int(n) for n, a, b in rows}) == 219, 'wrong DAG row count')
    nodes = {int(n): (edge(a), edge(b)) for n, a, b in rows}
    require(set(nodes) == set(range(219)), 'wrong source DAG domain')
    require('mkProg dag_nodes 0 219' in text, 'wrong source DAG root')
    require(nodes[130] == (('N', 123), ('N', 166)), 'unexpected original MP branch')
    require(nodes[197] == (('D', 4), ('N', 191)) and
            nodes[191] == (('I', 5), ('C', 2)), 'unexpected transfer helper197')
    return nodes


def well_formed(nodes, root):
    """Exact finite interface of RMEquiv.wfCheck, including escape bounds."""
    size = len(nodes)
    require(set(nodes) == set(range(size)) and root in nodes, 'noncontiguous source node table')
    visiting = set()
    @lru_cache(None)
    def bounds(e):
        kind = e[0]
        if kind != 'N':
            require(kind in ('I', 'D', 'B', 'C', 'H'), 'unknown source instruction')
            if kind in ('I', 'D'):
                require(0 <= e[1] < 9, 'out-of-range source register')
            if kind in ('B', 'C'):
                require(e[1] > 0, 'nonpositive control escape')
            return 0, (1 if kind == 'D' else e[1] if kind == 'B' else 0), (e[1] if kind == 'C' else 0)
        n = e[1]
        require(n in nodes and n not in visiting, 'out-of-range node or cyclic decoder tree')
        visiting.add(n)
        a, b = (bounds(x) for x in nodes[n])
        visiting.remove(n)
        return 1 + max(a[0], b[0]), max(a[1] - 1, b[1]), max(a[2], b[2] - 1)
    table = [bounds(('N', n)) for n in range(size)]
    H, B, C = (list(column) for column in zip(*table))
    require(H[root] <= size + 1 and B[root] == C[root] == 0, 'root WF or escape check failed')
    # Independently check the generated tables against all eight node inequalities.
    def h(e): return H[e[1]] if e[0] == 'N' else 0
    def b(e): return B[e[1]] if e[0] == 'N' else 1 if e[0] == 'D' else e[1] if e[0] == 'B' else 0
    def c(e): return C[e[1]] if e[0] == 'N' else e[1] if e[0] == 'C' else 0
    for n, (left, right) in nodes.items():
        require(h(left) < H[n] and h(right) < H[n], 'height inequality failed')
        require(b(left) <= B[n] + 1 and b(right) <= B[n], 'break bound failed')
        require(c(left) <= C[n] and c(right) <= C[n] + 1, 'continue bound failed')
    return {'root': root, 'nodes': size, 'root_height': H[root],
            'root_break_bound': B[root], 'root_continue_bound': C[root],
            'height_table': H, 'break_table': B, 'continue_table': C,
            'generic_theorems': ['RMEquiv.wfCheck_sound', 'RMEquiv.halts_iff_iterHalts']}


def unfold(nodes, root):
    @lru_cache(None)
    def expand(e):
        return ('N', *(expand(x) for x in nodes[e[1]])) if e[0] == 'N' else e
    return expand(('N', root))


def replace_subtree(tree, path, replacement):
    if not path:
        return replacement
    require(tree[0] == 'N', 'replacement path crosses a source leaf')
    side = int(path[0])
    children = list(tree[1:])
    children[side] = replace_subtree(children[side], path[1:], replacement)
    return 'N', *children


def leaves(tree, path=''):
    if tree[0] == 'N':
        yield from leaves(tree[1], path + '0')
        yield from leaves(tree[2], path + '1')
    else:
        yield path, tree


def tree_stats(tree):
    sites = list(leaves(tree))
    return {'leaves': len(sites), 'guards': sum(2 if e[0] == 'D' else 1 for p, e in sites),
            'maximum_leaf_depth': max(len(p) for p, e in sites),
            'operation_counts': dict(Counter(e[0] for p, e in sites))}


def increment(path):
    """Exact incPath: overflow preserves length and replaces all bits by0."""
    bits = list(path)
    i = len(bits) - 1
    while i >= 0 and bits[i] == '1':
        bits[i] = '0'
        i -= 1
    if i >= 0:
        bits[i] = '1'
    return ''.join(bits)


def strip(path, bit, count):
    i = len(path)
    while i and count:
        i -= 1
        count -= path[i] == bit
    return path[:i]


def encode_pointer(path):
    require(len(path) < 128, 'pointer exceeds retained Lean decode fuel')
    return int('1' + path, 2)


def decode_pointer(code):
    require(isinstance(code, int) and code >= 1, 'bad pointer code')
    path = bin(code)[3:]
    require(len(path) < 128, 'pointer exceeds retained Lean decode fuel')
    return path


class Program:
    def __init__(self, nodes, root):
        self.nodes, self.root = nodes, root

    @lru_cache(None)
    def site(self, pointer):
        e, depth, path = ('N', self.root), 0, ''
        while e[0] == 'N':
            require(depth <= len(self.nodes), 'decoder fuel exhausted')
            bit = int(pointer[depth]) if depth < len(pointer) else 0
            e = self.nodes[e[1]][bit]
            path += str(bit)
            depth += 1
        return e, path

    @lru_cache(None)
    def segment(self, pointer):
        """Literal translation of RMBisim.seg, not an RM state simulation."""
        increments, steps = [], 0
        for _ in range(SEGMENT_FUEL):
            e, consumed = self.site(pointer)
            if e[0] in ('D', 'H'):
                return tuple(increments), pointer, steps
            if e[0] == 'I':
                increments.append(e[1])
                pointer = increment(consumed)
            elif e[0] == 'B':
                pointer = increment(strip(consumed, '0', e[1]))
            elif e[0] == 'C':
                pointer = strip(consumed, '1', e[1])
            else:
                raise ValueError('unexpected source leaf in segment')
            steps += 1
        raise ValueError('segment fuel exhausted; this is a failed check')


def generate_certificate(first, second):
    l1, p1, _ = first.segment('')
    l2, p2, _ = second.segment('')
    require(Counter(l1) == Counter(l2), 'initial segment has different register effects')
    pairs, index, entries = [(p1, p2)], {(p1, p2): 0}, []
    cursor = 0
    while cursor < len(pairs):
        p1, p2 = pairs[cursor]
        e1, q1 = first.site(p1)
        e2, q2 = second.site(p2)
        require(e1 == e2 and e1[0] in ('D', 'H'), f'unmatched test sites at entry {cursor}')
        successors = []
        if e1[0] == 'H':
            successors = [0, 0]
        else:
            for zero in (False, True):
                a = increment(strip(q1, '0', 1)) if zero else increment(q1)
                b = increment(strip(q2, '0', 1)) if zero else increment(q2)
                x, a, _ = first.segment(a)
                y, b, _ = second.segment(b)
                require(Counter(x) == Counter(y), f'different branch effects at entry {cursor}')
                if (a, b) not in index:
                    index[a, b] = len(pairs)
                    pairs.append((a, b))
                successors.append(index[a, b])
        entries.append([encode_pointer(p1), encode_pointer(p2), *successors])
        cursor += 1
    return entries


def check_certificate(first, second, entries):
    """Validate all entries, including ones not needed by the generator's BFS."""
    require(entries and all(len(row) == 4 for row in entries), 'malformed certificate')
    pointers = [(decode_pointer(a), decode_pointer(b)) for a, b, j, k in entries]
    longest, distinct_vectors, ordered_differences = 0, set(), 0
    branch_count, test_count, halt_count = 0, 0, 0

    def branch(a, b, target):
        nonlocal longest, ordered_differences, branch_count
        require(isinstance(target, int) and 0 <= target < len(entries), 'certificate target out of range')
        l1, p1, n1 = first.segment(a)
        l2, p2, n2 = second.segment(b)
        require(Counter(l1) == Counter(l2), 'certificate increment-vector mismatch')
        require((p1, p2) == pointers[target], 'certificate successor-pointer mismatch')
        longest = max(longest, n1, n2)
        ordered_differences += l1 != l2
        distinct_vectors.add(tuple(Counter(l1).get(i, 0) for i in range(9)))
        branch_count += 1

    branch('', '', 0)
    for n, ((p1, p2), entry) in enumerate(zip(pointers, entries)):
        e1, q1 = first.site(p1)
        e2, q2 = second.site(p2)
        require(e1 == e2, f'certificate test label mismatch at {n}')
        if e1[0] == 'H':
            halt_count += 1
            continue
        require(e1[0] == 'D', f'certificate contains a non-test site at {n}')
        test_count += 1
        branch(increment(q1), increment(q2), entry[2])
        branch(increment(strip(q1, '0', 1)), increment(strip(q2, '0', 1)), entry[3])
    return {'entries': len(entries), 'matched_decrement_sites': test_count,
            'matched_halt_sites': halt_count, 'checked_branches_including_initial': branch_count,
            'maximum_increment_control_segment_steps': longest,
            'branches_with_different_increment_order_but_equal_counts': ordered_differences,
            'distinct_increment_vectors': len(distinct_vectors),
            'all_nine_register_effects_equal': True, 'both_decrement_outcomes_checked': True,
            'segment_fuel': SEGMENT_FUEL, 'all_pointer_codes_fit_128_bit_decode': True,
            'generic_theorems': ['RMBisim.seg_run', 'RMBisim.Bisim.halts_iff', 'RMBisim.check_halts_iff']}


def verify(directory, regenerate=None):
    dag = parse_dag(read_pinned(directory / 'Dag254.v', DAG_SHA))
    prog = parse_prog(read_pinned(directory / 'Prog254.v', PROG_SHA))
    decoder_data = json.loads(read_pinned(directory / 'mp-cache-permuted252.json', DECODER_SHA))
    decoder = {int(n): tuple(map(tuple, pair)) for n, pair in decoder_data['nodes'].items()}
    decoder_root = decoder_data['root']
    require(len(decoder) == 203 and decoder_root == 202, 'wrong new decoder domain')
    modified_dag = dict(dag)
    modified_dag[130] = dag[130][0], ('N', 197)
    require([n for n in dag if modified_dag[n] != dag[n]] == [130], 'source edit is not unique')
    source_wf = well_formed(modified_dag, 0)
    literal_wf = well_formed(prog, 0)
    decoder_wf = well_formed(decoder, decoder_root)
    source_tree, literal_tree, decoder_tree = unfold(dag, 0), unfold(prog, 0), unfold(decoder, decoder_root)
    helper_tree = unfold(dag, 197)
    expected = replace_subtree(literal_tree, REWRITE_PATH, helper_tree)
    require(expected == decoder_tree, 'full expanded decoder tree is not the specified one-subtree edit')
    old_sites, new_sites = dict(leaves(literal_tree)), dict(leaves(decoder_tree))
    require({p: e for p, e in old_sites.items() if not p.startswith(REWRITE_PATH)} ==
            {p: e for p, e in new_sites.items() if not p.startswith(REWRITE_PATH)},
            'a source leaf outside the success subtree changed')
    # Reproduce the retained baseline relation as a nontrivial calibration of
    # the exact path conventions, including commuting increment sequences.
    original_entries = generate_certificate(Program(dag, 0), Program(prog, 0))
    original_check = check_certificate(Program(dag, 0), Program(prog, 0), original_entries)
    require(original_check['entries'] == 3010, 'baseline 3010-pair relation was not reproduced')
    first, second = Program(modified_dag, 0), Program(decoder, decoder_root)
    if regenerate is not None:
        entries = generate_certificate(first, second)
        artifact = {'format': 'RMBisim.Entry list: [source pointer, decoder pointer, nonzero successor index, zero successor index]',
                    'pointer_encoding': 'binary1 followed by exact path bits, including trailing zeros',
                    'source_commit': PIN, 'dag_sha256': DAG_SHA, 'prog_sha256': PROG_SHA,
                    'decoder_sha256': DECODER_SHA,
                    'source_edit': {'node': 130, 'side': 'right', 'old': ['N', 166], 'new': ['N', 197]},
                    'entries': entries}
        regenerate.write_text(json.dumps(artifact, indent=2) + '\n')
        certificate_path = regenerate
    else:
        certificate_path = directory / 'source_binding_certificate.json'
        artifact = json.loads(certificate_path.read_text())
        require((artifact['dag_sha256'], artifact['prog_sha256'], artifact['decoder_sha256']) ==
                (DAG_SHA, PROG_SHA, DECODER_SHA), 'certificate source hashes mismatch')
        entries = artifact['entries']
    changed_check = check_certificate(first, second, entries)
    require(changed_check['entries'] == 2998, 'wrong edited relation size')
    # Corrupt a relation pointer and show that the semantic checker rejects it.
    broken = [list(row) for row in entries]
    broken[0][0] = encode_pointer('1111111111111111111111111111111111')
    rejected = False
    try:
        check_certificate(first, second, broken)
    except ValueError:
        rejected = True
    require(rejected, 'deliberately corrupted certificate was accepted')
    return {'status': 'all source-binding checks passed',
            'proof_scope': 'Ordinary complete segment bisimulation for every initial register file; no local Lean or Coq build is claimed',
            'source_commit': PIN, 'dag_sha256': DAG_SHA, 'prog_sha256': PROG_SHA,
            'decoder_sha256': DECODER_SHA,
            'exact_edit': {'source_node': 130, 'side': 'right', 'old_edge': ['N', 166],
                           'new_edge': ['N', 197], 'literal_decoder_prefix': REWRITE_PATH},
            'full_ordered_tree_equality_after_subtree_edit': True,
            'all_literal_leaves_outside_prefix_identical': True,
            'unmodified_dag_and_literal_trees_literally_equal': source_tree == literal_tree,
            'baseline_tree': tree_stats(literal_tree), 'new_decoder_tree': tree_stats(decoder_tree),
            'original_source_dag_tree': tree_stats(source_tree),
            'modified_source_well_formedness': source_wf,
            'literal_root_height': literal_wf['root_height'],
            'new_decoder_root_height': decoder_wf['root_height'],
            'baseline_segment_bisimulation': original_check,
            'new_segment_bisimulation': changed_check,
            'certificate_sha256': sha(certificate_path.read_bytes()),
            'corrupted_certificate_rejected': rejected,
            'conclusion': 'For every register file R, the exact audited new decoder halts from empty path and R iff the219-node structured DAG with only130.right replaced by197 does so.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--regenerate-certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.directory, args.regenerate_certificate)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    brief = {k: result[k] for k in ('status', 'dag_sha256', 'prog_sha256', 'decoder_sha256',
                                   'full_ordered_tree_equality_after_subtree_edit',
                                   'new_segment_bisimulation', 'certificate_sha256',
                                   'corrupted_certificate_rejected', 'conclusion')}
    print(json.dumps(brief, indent=2))


if __name__ == '__main__':
    main()
