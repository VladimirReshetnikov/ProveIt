#!/usr/bin/env python3
"""Deterministically reconstruct and check K_s223 from the frozen K224 packet.

No search or optimization is run. The source is reconstructed from an explicit
closed-macro grammar; its numerical stack expression is checked independently;
all primitive macro contracts are linked to pinned Dag230 by finite all-register
bisimulations. The table is rebuilt by deterministic reuse of obsolete decoder
labels and checked against the intended subtree at every decoded source prefix.

This is an executable ordinary mathematical certificate, not a new Rocq/Lean
kernel endpoint. The uniform K_s/equality interpretation and the unbounded
binary runtime are separate necessary obligations, supplied by the packet.

Usage: python3 -B build223.py --baseline-root <unpacked-K224-root> --output <new-dir>
"""
from pathlib import Path
from collections import defaultdict
from functools import cache
import argparse
import hashlib
import io
import json
import re
import sys
import zipfile
import source_language as s
from local_bisimulation import check as bisimulation

HERE = Path(__file__).resolve().parent
TARGET = '11101001001110'
HALT = 254
PINS = {
    'portable/machine/results/candidate224.k.tm': 'f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f',
    'portable/machine/results/sites.json': '309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878',
    'portable/machine/reference/legacy_state_map.json': '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151',
    'portable/vendor/K225_Construction_2026-10-19.zip': '75b58ce7b5840ef3a3158341f7cf1e601aab67d19ab147d96cf37d1186cb6cbc',
}
EXPECTED = {
    'candidate.k.tm': '7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef',
    'candidate.legacy.tm': '2d83dd47e1aedd4ed89f6a97d55e2ef6942fca39d55f8bb397536e64702715c3',
    'candidate223.tm': 'c89d3f79ab12a3857092bb4b3d30bfc594079edc0f696b066ce4c386fd00f1b2',
    'sites.json': 'df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c',
}
GRAMMAR_SHA = '8b8dd4e165d8a08f7def72eca7f345da231aa3f0c7e318f3e23fddfa8b368f6a'
DAG_FILE = 'K225_Construction_2026-10-19/portable/baseline226/vendor/k230-rocq/coq/prog/Dag230.v'
DAG_SHA = '7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def tuple_tree(value):
    return tuple(map(tuple_tree, value)) if isinstance(value, list) else value


def read_table(raw):
    rows = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need((q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad table row')
        rows[q, b] = (w, 1 if d == 'R' else -1, target)
    need(starts == [0], 'Expected K-labelled start0')
    states = {q for q, b in rows}
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    need({t for w, d, t in rows.values()} - states == {HALT}, 'Unexpected terminal state')
    return rows


def table_bytes(rows, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {target}\n'
        for (q, b), (w, d, target) in sorted(rows.items()))).encode('ascii')


def decoder_map(table, tree):
    """Read every internal-node prefix using only its actual known tape bits.

    The caller must also compare the returned q/subtree relation to the intended
    relation. Merely reaching an arbitrary state is not sufficient validation.
    """
    groups = defaultdict(set)
    paths = defaultdict(list)
    def visit(node, prefix, state):
        if s.leaf(node):
            return
        groups[state].add(node); paths[state].append(prefix)
        for bit in (0, 1):
            if s.leaf(node[bit]):
                continue
            tape = {i: int(value) for i, value in enumerate(prefix + str(bit))}
            tape[-1] = 1
            before = tape.copy()
            head, q = len(prefix), state
            for tick in range(100):
                if head == len(prefix) + 1:
                    break
                need(head in tape, 'Decoder read outside known prefix')
                w, d, q = table[q, tape[head]]
                tape[head] = w; head += d
            need(tape == before and head == len(prefix) + 1, 'Decoder prefix changed or did not advance')
            visit(node[bit], prefix + str(bit), q)
    visit(tree, '', 84)
    return groups, paths


def sole(groups, state):
    need(len(groups[state]) == 1, 'Expected one represented subtree at ' + str(state))
    return next(iter(groups[state]))


def closed_chunks(tree, first, last):
    result = []
    def visit(node, start):
        end = start + len(s.sites(node))
        if end <= first or start >= last:
            return
        if first <= start and end <= last:
            need(s.boundary(node) == (0, 0, False), 'Cut chunk is not closed')
            result.append(node); return
        need(not s.leaf(node), 'Cut does not align to instructions')
        visit(node[0], start)
        visit(node[1], start + len(s.sites(node[0])))
    visit(tree, 0)
    return result


def sequence(nodes):
    need(bool(nodes), 'Empty sequence')
    result = nodes[-1]
    for node in reversed(nodes[:-1]):
        result = node, result
    return result


def I(x, y): return 'I', x, y

def Q(x, y): return 'Q', x, y

def R(x, y): return 'R', x, y

def E(x, y): return 'E', x, y

def N(x): return I(x, 1)


def expected_expression():
    """Direct fused K_s expression, independent of a rewriting/search program."""
    a, b, c = 'a', 'b', 'c'
    member = R(b, c)
    subset = Q(c, I(R(c, a), R(c, b)))
    found = N(Q(b, I(c, N(member))))
    request = Q(b, I(c, found))
    closure = Q(a, I(subset, request))
    support = N(Q(a, I(c, N(closure))))
    hereditary = Q(b, I(member, support))
    membership_vacuity = I(R(a, b), Q(c, R(a, b)))
    equality_helper = I(E(a, b), Q(R(a, b), E(a, b)))
    return N(I(membership_vacuity,
               I(equality_helper, Q(c, I(hereditary, N(request))))))


def execute_word(word):
    top, stack = 'previous_top', ['arbitrary_older_stack']
    for macro in word:
        if macro in (166, 121, 168, 177):
            stack.append(top)
            top = {166: 'a', 121: 'b', 168: 'c', 177: 1}[macro]
        elif macro == 218:
            top = N(top)
        else:
            need(macro in (119, 180, 181, 182) and len(stack) >= 2, 'Bad constructor word')
            top = {119: I, 180: Q, 181: R, 182: E}[macro](stack.pop(), top)
    need(stack == ['arbitrary_older_stack', 'previous_top'], 'Emitter corrupts surrounding stack')
    return top


def macros_and_contracts(baseline, groups):
    inc = ('CI', 1)
    pa, pb, pc = sole(groups, 98), sole(groups, 12), sole(groups, 166)
    imp, negation = sole(groups, 90), sole(groups, 184)
    one = negation[0]
    macros = {166: pa, 121: pb, 168: pc, 177: one, 119: imp,
              180: (imp, (inc, inc)), 181: (imp, inc),
              182: (imp, ((inc, inc), inc)), 218: negation}
    need(negation == (one, imp), 'Negation macro structure changed')
    archive = baseline / 'portable/vendor/K225_Construction_2026-10-19.zip'
    with zipfile.ZipFile(archive) as packet:
        raw = packet.read(DAG_FILE)
    need(sha(raw) == DAG_SHA, 'Pinned Dag230 source differs')
    dag = {int(q): (a, b) for q, a, b in re.findall(
        r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)', raw.decode())}
    @cache
    def expand(q):
        def edge(text):
            if text == 'EHalt':
                return 'CH', None
            kind, argument = text.split(); argument = int(argument)
            if kind == 'ENode':
                return expand(argument)
            return {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB', 'EContinue': 'CC'}[kind], argument
        return tuple(edge(text) for text in dag[q])
    contracts = {str(q): bisimulation(expand(q), macro) for q, macro in macros.items()}
    need(all(s.boundary(macro) == (0, 0, False) for macro in macros.values()), 'Macro is not closed')
    tokens = {q: [macro] for q, macro in macros.items()}
    for q in (166, 121, 168):
        tokens[q] = list(macros[q])
    tokens.update({180: [imp, inc, inc], 181: [imp, inc],
                   182: [imp, inc, inc, inc], 218: [one, imp]})
    for q, pieces in tokens.items():
        need(all(s.boundary(t) == (0, 0, False) for t in pieces), 'Split macro part is not closed')
        bisimulation(macros[q], sequence(pieces))
    return tokens, contracts


def build_source(baseline, oldtree, groups, spec):
    tokens, contracts = macros_and_contracts(baseline, groups)
    oldax = s.subtree(oldtree, TARGET)
    need(len(s.sites(oldax)) == 4004, 'Old emitter census changed')
    prefix = closed_chunks(oldax, 0, 1893)
    suffix = closed_chunks(oldax, 3970, 4004)
    need(len(prefix) == 6 and len(suffix) == 2, 'Old closed boundary decomposition changed')
    word = spec['macro_word']
    expression = execute_word(word)
    need(len(word) == 77 and expression == expected_expression(), 'Literal numerical emitter does not compute K_s bundle')
    need(expression == tuple_tree(spec['expression']), 'Stored expression differs')
    units = prefix + sum((tokens[q] for q in word), []) + suffix
    need(len(units) == len(spec['units']) == 164, 'Wrong unit count')
    for unit, record in zip(units, spec['units']):
        need(s.boundary(unit) == (0, 0, False), 'Unit is not closed')
        need(len(s.sites(unit)) == record['leaves'] and sha(s.compact(s.sites(unit))) == record['source_sha256'], 'Unit pin differs')
    ordinal = []
    def assemble(pattern):
        if type(pattern) is int:
            need(pattern == len(ordinal) and pattern < len(units), 'Grammar permutes or duplicates units')
            ordinal.append(pattern); return units[pattern]
        need(isinstance(pattern, list) and len(pattern) == 2, 'Malformed binary grammar')
        return assemble(pattern[0]), assemble(pattern[1])
    ax = assemble(spec['pattern'])
    need(ordinal == list(range(len(units))), 'Grammar drops units')
    tree = s.replace(oldtree, TARGET, ax)
    reference = s.replace(oldtree, TARGET, sequence(units))
    source, reference_source = s.sites(tree), s.sites(reference)
    need([r[1:] for r in source] == [r[1:] for r in reference_source], 'Source instruction order changed')
    graph, checks = s.graph_arithmetic(source)
    ref_graph, ref_checks = s.graph_arithmetic(reference_source)
    need(graph == ref_graph == s.graph_intervals(source) == s.graph_intervals(reference_source), 'Complete guarded graphs differ')
    need(s.metrics(tree) == {'dag_nodes': 209, 'leaf_occurrences': 4962, 'maximum_depth': 37, 'maximum_zero_run': 6}, 'Unexpected source metrics')
    return tree, {'status': 'EXACT_NUMERICAL_EMITTER_AND_CLOSED_GRAMMAR_PASS',
                  'macro_word': word, 'expression': expression, 'contracts': contracts,
                  'unit_count': len(units), 'candidate_cfg_checks': checks,
                  'reference_cfg_checks': ref_checks, 'guarded_cfg_equal': True,
                  'scope': 'All natural a,b,c and arbitrary earlier top/stack, with the inherited clean-scratch macro interface.'}


def build_table(old, oldtree, groups, tree):
    nodes = set()
    def collect(node):
        if node in nodes or s.leaf(node): return
        nodes.add(node); collect(node[0]); collect(node[1])
    collect(tree)
    oldmap = {node: q for q, alternatives in groups.items() for node in alternatives}
    intended = {node: oldmap[node] for node in nodes if node in oldmap}
    occupied = set(intended.values())
    def align(before, after, path=''):
        if s.leaf(before) or s.leaf(after): return
        q = oldmap[before]
        if after not in intended and q not in occupied and len(groups[q]) == 1:
            intended[after] = q; occupied.add(q)
        if path == TARGET: return
        if TARGET.startswith(path):
            align(before[0], after[0], path + '0')
            align(before[1], after[1], path + '1')
    align(oldtree, tree)
    free = sorted(set(groups) - occupied,
                  key=lambda q: (any(d != 1 or w != b for b, (w, d, t) in enumerate((old[q, 0], old[q, 1]))), q))
    def assign(node):
        if s.leaf(node): return
        if node not in intended:
            need(bool(free), 'Construction would need a new state')
            intended[node] = free.pop(0)
        assign(node[0]); assign(node[1])
    assign(tree)
    table = dict(old)
    def leaf_row(node, bit):
        op, arg = node
        if op == 'CI' and arg == 1: return bit, 1, 61
        if op == 'CB' and arg == 1 and bit == 1: return 0, -1, 40
        if op == 'CH' and bit == 1: return 1, 1, HALT
        if op == 'CD' and bit == 0: return 0, 1, {0: 14, 1: 41, 2: 56, 3: 17, 4: 144, 5: 45, 6: 21, 7: 62, 8: 39}[arg]
        if op == 'CI': return bit, 1, {0: 14, 1: 61, 2: 56, 3: 161, 4: 71, 5: 63, 6: 13, 7: 82, 8: 39}[arg]
        if op == 'CC' and bit == 1: return 0, -1, {1: 1, 2: 16, 3: 42}[arg]
        raise ValueError(('No supported new leaf entry', node, bit))
    for node, q in intended.items():
        if node in oldmap: continue
        for bit, child in enumerate(node):
            alternatives = groups.get(q, set())
            if len(alternatives) == 1 and next(iter(alternatives))[bit] == child:
                continue  # Keep every literal detail of the inherited helper role.
            table[q, bit] = leaf_row(child, bit) if s.leaf(child) else (bit, 1, intended[child])
    need(intended[tree] == 84, 'Source root label changed')
    reachable, pending = {0}, [0]
    while pending:
        q = pending.pop()
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != HALT and target not in reachable:
                reachable.add(target); pending.append(target)
    table = {key: row for key, row in table.items() if key[0] in reachable}
    need(len(reachable) == 223 and len(table) == 446, 'Wrong final table census')
    need({q for q, bit in old} - reachable == {227}, 'Unexpected deleted state')
    actual, paths = decoder_map(table, tree)
    expected = defaultdict(set)
    for node, q in intended.items(): expected[q].add(node)
    need(set(actual) == set(expected), 'Decoder state inventory differs')
    for q, alternatives in actual.items():
        need(alternatives == expected[q], 'Decoder reached an unintended subtree at ' + str(q))
    edits = [{'q': q, 'bit': bit, 'old': list(old[q, bit]), 'new': list(row)}
             for (q, bit), row in sorted(table.items()) if old[q, bit] != row]
    need(len(edits) == 36, 'Wrong retained-row edit count')
    return table, {'status': 'EXACT_TABLE_AND_INTENDED_DECODER_RELATION_PASS',
                   'working_states': 223, 'rows': 446, 'deleted_k_states': [227],
                   'changed_retained_rows': 36, 'edits': edits,
                   'decoder_states': len(actual), 'decoder_subtrees': sum(map(len, actual.values())),
                   'contextual_alias_savings': sum(len(v) - 1 for v in actual.values()),
                   'prefix_occurrences': sum(map(len, paths.values())),
                   'scope': 'Exact source-prefix relation. Complete instruction execution and blank startup require the separate runtime audit.'}


def canonicalize(table):
    order, mapping = [0], {0: 0}
    for q in order:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != HALT and target not in mapping:
                mapping[target] = len(order); order.append(target)
    need(len(order) == 223, 'Canonical graph census')
    mapping[HALT] = 223
    return {(mapping[q], bit): (w, d, mapping[target])
            for (q, bit), (w, d, target) in table.items()}, mapping


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-root', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--grammar', type=Path, default=HERE / 'grammar223.json',
                    help='Literal grammar certificate; defaults beside this script')
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    baseline, output = args.baseline_root.resolve(), args.output.resolve()
    need(not output.exists() or (output.is_dir() and not any(output.iterdir())), 'Output must be initially empty')
    output.mkdir(parents=True, exist_ok=True)
    for name, expected in PINS.items():
        need(sha((baseline / name).read_bytes()) == expected, 'Pinned baseline input differs: ' + name)
    raw_spec = args.grammar.read_bytes()
    need(sha(raw_spec) == GRAMMAR_SHA, 'Grammar certificate differs')
    spec = json.loads(raw_spec)
    old = read_table((baseline / 'portable/machine/results/candidate224.k.tm').read_bytes())
    oldtree = s.tree(json.loads((baseline / 'portable/machine/results/sites.json').read_text()))
    groups, paths = decoder_map(old, oldtree)
    need(len(groups) == 175 and sum(map(len, groups.values())) == 187, 'Old decoder census differs')
    tree, source_receipt = build_source(baseline, oldtree, groups, spec)
    table, table_receipt = build_table(old, oldtree, groups, tree)
    canonical, mapping = canonicalize(table)
    legacy_raw = json.loads((baseline / 'portable/machine/reference/legacy_state_map.json').read_text())
    legacy = {int(q): target for q, target in legacy_raw['k230_to_old'].items()}
    legacy[HALT] = HALT
    legacy_table = {(legacy[q], bit): (w, d, legacy[target]) for (q, bit), (w, d, target) in table.items()}
    artifacts = {'candidate.k.tm': table_bytes(table), 'candidate223.tm': table_bytes(canonical),
                 'candidate.legacy.tm': table_bytes(legacy_table, legacy[0]), 'sites.json': s.compact(s.sites(tree))}
    for name, raw in artifacts.items():
        need(sha(raw) == EXPECTED[name], 'Reconstruction hash differs: ' + name)
        (output / name).write_bytes(raw)
    dump(output / 'canonical_map.json', {'k_to_canonical': mapping,
         'canonical_to_k': {v: k for k, v in mapping.items()},
         'start_k': 0, 'halt_k': HALT, 'start_canonical': 0, 'halt_canonical': 223})
    dump(output / 'source_certificate.json', source_receipt)
    dump(output / 'table_certificate.json', table_receipt)
    result = {'status': 'DETERMINISTIC_223_RECONSTRUCTION_PASS', 'artifacts': EXPECTED,
              'working_states': 223, 'rows': 446, 'source_metrics': s.metrics(tree),
              'macro_contracts': len(source_receipt['contracts']), 'guarded_cfg_checks': source_receipt['candidate_cfg_checks'],
              'contextual_alias_savings': table_receipt['contextual_alias_savings'],
              'proof_status': 'Ordinary mathematical source/table certificates. Requires the packet K_s native interpretation and unbounded binary runtime. No new proof-assistant endpoint.'}
    dump(output / 'reconstruction.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
