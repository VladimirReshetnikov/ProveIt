#!/usr/bin/env python3
"""Independent G223 source audit against the literal K224 source.

This checker does not import construct_g226.py, check_g_emitter.py, their
receipts, or the grammar search.  It reconstructs the two formula words,
checks every primitive instruction, and proves the entire changed closed
source block bisimilar for all register values.  Binary runtime and logical
calculus calibration are deliberately outside this source-level certificate.
"""
from pathlib import Path
from functools import cache, reduce
import argparse, hashlib, json, re, sys

def require(value, message):
    if not value:
        raise ValueError(message)

def I(x, y): return ('I', x, y)
def R(x, y): return ('R', x, y)
def E(x, y): return ('E', x, y)
def Q(x, y): return ('Q', x, y)
def N(x): return I(x, 1)
def A(x, y): return N(I(x, N(y)))
def XA(v, x, y): return N(Q(v, I(x, N(y))))

def expressions():
    a, b, c = 'a', 'b', 'c'
    subset = Q(c, I(R(c, a), R(c, b)))
    request = Q(b, I(c, XA(b, c, R(b, c))))
    support = XA(a, c, Q(a, I(subset, request)))
    core = XA(c, I(c, R(b, c)), Q(b, I(R(b, c), support)))
    rv = I(R(a, b), Q(c, R(a, b)))
    ev = I(E(a, b), Q(R(a, b), E(a, b)))
    old_row = I(E(c, a), I(E(c, b), E(a, b)))
    new_row = I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b))))
    old_bundle = N(I(core, I(rv, N(ev))))
    new_bundle = A(core, rv)
    return old_row, new_row, old_bundle, new_bundle

def emit(expression):
    if isinstance(expression, str):
        return ({'a': 166, 'b': 121, 'c': 168}[expression],)
    if expression == 1:
        return (177,)
    op, x, y = expression
    if op == 'I' and y == 1:
        return emit(x) + (218,)
    return emit(x) + emit(y) + ({'I': 119, 'R': 181, 'Q': 180, 'E': 182}[op],)

def execute(word):
    # The retained marker represents an arbitrary prior top and older stack.
    stack = ['arbitrary prior top and stack']
    for op in word:
        if op in (166, 121, 168, 177):
            stack.append({166: 'a', 121: 'b', 168: 'c', 177: 1}[op])
        elif op == 218:
            require(len(stack) >= 2, 'Neg underflow')
            stack[-1] = N(stack[-1])
        else:
            require(len(stack) >= 3, 'Binary constructor underflow')
            y, x = stack.pop(), stack.pop()
            stack.append({119: I, 181: R, 180: Q, 182: E}[op](x, y))
    require(len(stack) == 2 and stack[0] == 'arbitrary prior top and stack',
            'Incorrect symbolic stack effect')
    return stack[1]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline-root', '--baseline224', dest='baseline224',
                   type=Path, required=True,
                   help='Extracted K224_Construction_2026-10-20 directory')
    p.add_argument('--upstream226', type=Path, required=True)
    p.add_argument('--sites', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled; do not use -O')
    sys.path.insert(0, str(args.upstream226 / 'verification'))
    import reconstruct227 as c
    sys.path.insert(0, str(args.baseline224 / 'portable/verification'))
    import construct_rel225 as cr
    import local_bisimulation as lb

    baseline_path = args.baseline224 / 'portable/machine/results/sites.json'
    digest = lambda data: hashlib.sha256(data).hexdigest()
    require(digest(baseline_path.read_bytes()) ==
            '309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878',
            'Pinned K224 source differs')
    base = c.tree(json.loads(baseline_path.read_text()))
    final = c.tree(json.loads(args.sites.read_text()))
    parent = c.tree(json.loads((args.baseline224 / 'portable/parent225/sites225.json').read_text()))
    parent_table = cr.read_table(args.baseline224 / 'portable/parent225/candidate225.k.tm')
    groups, _ = cr.decoder_map(c, parent_table, parent)
    old = lambda q: cr.sole(groups, q)

    @cache
    def flat(n):
        return (n,) if c.leaf(n) else flat(n[0]) + flat(n[1])

    # These macro implementations are taken exclusively from the pinned
    # baseline, then checked against the upstream arithmetic macro programs.
    macros = {166: old(98), 121: old(12), 168: old(166), 177: old(184)[0],
              119: old(90), 180: old(86), 181: (old(90), ('CI', 1)),
              182: (old(90), (('CI', 1), (('CI', 1), ('CI', 1)))),
              218: old(184)}
    dag_file = args.upstream226 / 'vendor/k230-rocq/coq/prog/Dag230.v'
    require(digest(dag_file.read_bytes()) ==
            '7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf',
            'Pinned upstream macro DAG differs')
    data = dag_file.read_text()
    dag = {int(n): (x, y) for n, x, y in re.findall(
        r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)', data)}
    @cache
    def expand_edge(edge):
        if edge == 'EHalt':
            return ('CH', None)
        tag, text = edge.split()
        v = int(text)
        if tag == 'ENode':
            return tuple(expand_edge(x) for x in dag[v])
        return ({'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB', 'EContinue': 'CC'}[tag], v)
    contracts = {}
    for n, implementation in macros.items():
        reference = expand_edge('ENode ' + str(n))
        require(c.boundary(reference) == c.boundary(implementation) == (0, 0, False),
                'Open arithmetic constructor')
        contracts[n] = lb.check(reference, implementation)

    def word_flat(word):
        return tuple(v for n in word for v in flat(macros[n]))
    old_row, new_row, old_bundle, new_bundle = expressions()
    words = tuple(emit(f) for f in expressions())
    for f, word in zip(expressions(), words):
        require(execute(word) == f, 'Independent symbolic execution differs')
    r0, r1, k0, k1 = map(word_flat, words)
    before, after = flat(base), flat(final)
    require(flat(parent) == before, 'K224 and its parent primitive words differ')
    require(before[486:786] == r0, 'Baseline equality row differs')
    require(before[2541:4618] == k0, 'Baseline K bundle differs')
    expected = before[:486] + r1 + before[786:2541] + k1 + before[4618:]
    require(expected == after, 'Literal candidate source contains an undeclared change')

    # The two changes lie inside one closed block of the ACTUAL K224 tree.
    # Source outside that block is compared as a tree, not merely as a word.
    path = '11101001001110'
    def at(n, p):
        for bit in p:
            n = n[int(bit)]
        return n
    def replace_at(n, p, value):
        if not p:
            return value
        bit = int(p[0]); children = list(n)
        children[bit] = replace_at(children[bit], p[1:], value)
        return tuple(children)
    old_block, new_block = at(base, path), at(final, path)
    require(replace_at(final, path, old_block) == base,
            'Candidate changes source outside the common closed block')
    require(c.boundary(old_block) == c.boundary(new_block) == (0, 0, False),
            'Edited source block has an external branch')

    def cut(lo, hi):
        pieces = []
        def visit(n, pos):
            end = pos + len(flat(n))
            if end <= lo or pos >= hi:
                return
            if lo <= pos and end <= hi and c.boundary(n) == (0, 0, False):
                pieces.append(n)
                return
            require(not c.leaf(n), 'Reference cut crosses an open instruction')
            visit(n[0], pos); visit(n[1], pos + len(flat(n[0])))
        visit(old_block, 0)
        require(tuple(v for n in pieces for v in flat(n)) == flat(old_block)[lo:hi],
                'Closed factors do not cover exact reference interval')
        return pieces

    # The first two increments finish Eq(c,b).  Replace only the following
    # Eq(a,b) with Rel(a,b); Eq(a,b); All.  The second edit replaces the full K.
    require(flat(old_block)[2:84] == word_flat((166, 121, 182)), 'Incorrect equality tail')
    factors = (cut(0, 2) + [macros[n] for n in (166, 121, 181, 166, 121, 182, 180)]
               + cut(84, 1893) + [macros[n] for n in words[3]] + cut(3970, 4004))
    require(all(c.boundary(n) == (0, 0, False) for n in factors), 'Reference has an open factor')
    reference = reduce(lambda x, y: (x, y), factors)
    require(flat(reference) == flat(new_block), 'Reference instruction word differs')
    all_register_proof = lb.check(reference, new_block)
    source_graph, source_guards = c.graph_arithmetic(c.sites(final))
    require(source_graph == c.graph_intervals(c.sites(final)), 'Source CFG resolvers disagree')

    report = {
        'status': 'INDEPENDENT_K223_LITERAL_EMITTER_AND_ALL_REGISTER_SOURCE_BINDING_PASS',
        'source_sha256': digest(args.sites.read_bytes()),
        'baseline224_source_sha256': digest(baseline_path.read_bytes()),
        'source_metrics': c.metrics(final),
        'old_and_new_equality_row': [old_row, new_row],
        'old_and_new_K_bundle': [old_bundle, new_bundle],
        'formula_words': {'old_row': words[0], 'new_row': words[1],
                          'old_bundle': words[2], 'new_bundle': words[3]},
        'primitive_counts': {'old_row': len(r0), 'new_row': len(r1),
                             'old_bundle': len(k0), 'new_bundle': len(k1),
                             'old_source': len(before), 'new_source': len(after)},
        'all_other_primitive_instructions_unchanged': True,
        'common_closed_source_path': path,
        'source_tree_outside_closed_block_unchanged': True,
        'closed_reference_factors': len(factors),
        'all_register_closed_block_bisimulation': all_register_proof,
        'macro_contract_bisimulations': contracts,
        'complete_source_guards': source_guards,
        'independent_source_resolvers_agree': True,
        'gate_retained': 'c=a or c=b gives0; otherwise And(core_f(a,b,c),RV(a,b,c))',
        'scope': ('Exact literal source, all-natural arithmetic constructor expressions, '
                  'all-register closed-block equivalence and complete source CFG. '
                  'No G226 constructor, G emitter checker or their receipts imported. '
                  'Calculus equivalence, binary runtime and state folds are separate proofs.')}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'source_sha256', 'source_metrics',
          'primitive_counts', 'closed_reference_factors', 'complete_source_guards')}, indent=2))

if __name__ == '__main__':
    main()
