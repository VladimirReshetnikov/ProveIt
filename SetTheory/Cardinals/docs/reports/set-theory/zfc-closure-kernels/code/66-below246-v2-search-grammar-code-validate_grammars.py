#!/usr/bin/env python3
"""Check abstract grammar artifacts; this is deliberately not a TM verifier.

Run from any working directory. All inputs are located relative to this file.
The source-expression depth calculation follows the searcher's AST replacement
convention, including the documented fallback for deleted nonroot words.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter, defaultdict
import heapq
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = json.loads((ROOT / 'inputs/closed-sequence-grammar.json').read_text())


def parse_initial(mode):
    lines = (ROOT / 'inputs' / (mode + '.txt')).read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    symbols = json.loads((ROOT / 'inputs' / (mode + '-symbols.json')).read_text())
    encode = {v: k for k, v in symbols.items()}
    flat = SOURCE['flattened_' + mode + '_words']
    rules, names = {}, {}
    for line in lines[1:n+1]:
        k, w, q = line.split()
        k = int(k)
        assert w == ''.join(encode[t] for t in flat[q])
        left = str(SOURCE['rules'][q][0])
        assert k == (len(flat[left]) if left in flat else 1)
        rules[w] = (w[:k], w[k:])
        names[int(q)] = w
    roots = lines[n+1:n+1+nr]
    allowed = {c: int(m) for c, m in
               (line.split() for line in lines[n+1+nr:n+1+nr+na])}
    assert len(rules) == 127 and len(roots) == 24
    assert set(roots) == {names[q] for q in SOURCE['required_entry_roots']}
    return rules, names, roots, allowed


@lru_cache(None)
def footprint(ast):
    row = SOURCE['ast_dag'][ast]
    if row[0] == 'L':
        op, *arg = row[1]
        return (sum(1 << x for x in arg) if op in ('inc', 'dec') else 0,
                op == 'halt')
    a, ah = footprint(row[1])
    b, bh = footprint(row[2])
    return a | b, ah or bh


SYMBOLS = json.loads((ROOT / 'inputs/semantic-symbols.json').read_text())
REVERSE = {v: k for k, v in SYMBOLS.items()}
FP = {}
for char, name in SYMBOLS.items():
    mask, halt = footprint(SOURCE['atoms'][name]['ast'])
    FP[char] = 511 if halt else mask
    assert FP[char] != 0


def canonical(word):
    """Lexicographically first linear extension of register dependence chains."""
    last = [-1] * 9
    children = [[] for _ in word]
    indegree = [0] * len(word)
    for i, char in enumerate(word):
        predecessors = set()
        for r in range(9):
            if FP[char] & (1 << r):
                if last[r] >= 0:
                    predecessors.add(last[r])
                last[r] = i
        for j in predecessors:
            children[j].append(i)
            indegree[i] += 1
    queue = [(c, i) for i, c in enumerate(word) if not indegree[i]]
    heapq.heapify(queue)
    out = []
    while queue:
        char, i = heapq.heappop(queue)
        out.append(char)
        for j in children[i]:
            indegree[j] -= 1
            if not indegree[j]:
                heapq.heappush(queue, (word[j], j))
    assert len(out) == len(word)
    return ''.join(out)


def properties(rules, old, names, normalize):
    by_ast = {int(a): normalize(names[int(q)])
              for q, a in SOURCE['sequence_ast_roots'].items()}

    def join(a, b):
        return 1 + a[0], max(1 + a[0], a[1], b[1]), 1 + max(a[2], b[2])

    @lru_cache(None)
    def atom(ast):
        if ast in by_ast:
            return word(by_ast[ast])
        row = SOURCE['ast_dag'][ast]
        return (0, 0, 0) if row[0] == 'L' else join(atom(row[1]), atom(row[2]))

    @lru_cache(None)
    def word(w):
        if len(w) == 1:
            return atom(SOURCE['atoms'][SYMBOLS[w]]['ast'])
        a, b = rules[w] if w in rules else old[w]
        return join(word(a), word(b))

    return atom(SOURCE['original_ast'])


def validate(name, mode='semantic', commute=False, constrained=False,
             projection_count=18, depth_limit=40):
    data = json.loads((ROOT / 'results' / (name + '.json')).read_text())
    old, names, roots, allowed = parse_initial(mode)
    normal = canonical if commute else lambda s: s
    old = {normal(w): tuple(map(normal, children)) for w, children in old.items()}
    rules = {w: (a, b) for w, a, b in data['rules']}
    assert len(rules) == len(data['rules']) == data['rules_count']
    assert set(data['roots']) == {normal(w) for w in roots}
    for w, (a, b) in rules.items():
        assert len(w) == len(a) + len(b)
        assert w == normal(a + b), (name, 'wrong composition', w)
        for bit, child in enumerate((a, b)):
            assert len(child) == 1 or child in rules
            if data['observed_orientation_guards'] and len(child) == 1:
                assert allowed[child] & (1 << bit)
    visited = set()

    def visit(w):
        if len(w) == 1 or w in visited:
            return
        visited.add(w)
        for child in rules[w]:
            visit(child)

    for root in data['roots']:
        visit(root)
    assert visited == set(rules), (name, 'unreachable charged rules')
    out = dict(file=name + '.json', abstract_validation='PASS',
               tm_correctness='NOT_ESTABLISHED', rules=len(rules),
               seed=data['seed'], proposals=data['iterations'],
               terminal_orientation_guards=data['observed_orientation_guards'],
               commuting_word_keys=commute)
    if mode == 'semantic':
        lead, zeros, depth = properties(rules, old, names, normal)
        out['search_AST_properties'] = dict(leading_zeros=lead,
                                           maximum_zero_run=zeros, depth=depth)
        if constrained:
            constraint_source = SOURCE if projection_count == 18 else json.loads(
                (ROOT / 'inputs/closed-sequence-grammar-next22.json').read_text())
            constraints = constraint_source['left_entry_projection_constraints']
            assert len(constraints) == projection_count
            for c in constraints:
                q = normal(names[c['root']])
                for bit in c['prefix']:
                    q = rules[q][int(bit)]
                expected = normal(''.join(REVERSE[t] for t in c['word']))
                assert q == expected, (name, c, q, expected)
            assert zeros <= 7 and depth <= depth_limit
            out['partial_projection_constraints_checked'] = len(constraints)
            out['conservative_depth_guard'] = depth_limit
    return out


def main():
    results = [
        validate('physical-best', mode='physical'),
        validate('semantic-best'),
        validate('semantic-best2'),
        validate('semantic-context-best', constrained=True),
        validate('semantic-scan-best', constrained=True),
        validate('commutation-best', commute=True, constrained=True),
        validate('semantic-wide-best', constrained=True,
                 projection_count=22, depth_limit=64),
    ]
    target = ROOT / 'results/abstract-validation.json'
    target.write_text(json.dumps(results, indent=2) + '\n')
    pairs = Counter()
    flat = SOURCE['flattened_semantic_words']
    for root in SOURCE['required_entry_roots']:
        word = flat[str(root)]
        for a, b in zip(word, word[1:]):
            if not FP[REVERSE[a]] & FP[REVERSE[b]]:
                pairs[a, b] += 1
    groups = defaultdict(list)
    for q, word in flat.items():
        groups[canonical(''.join(REVERSE[t] for t in word))].append(int(q))
    census = dict(
        status='ABSTRACT_COMMUTATION_ANALYSIS_ONLY',
        adjacent_independent_occurrences=sum(pairs.values()),
        distinct_independent_pairs=len(pairs),
        pairs=[dict(left=a, right=b, occurrences=n)
               for (a, b), n in sorted(pairs.items())],
        existing_word_classes_with_multiple_states=[q for q in groups.values()
                                                  if len(q) > 1])
    (ROOT / 'results/commutation-census.json').write_text(
        json.dumps(census, indent=2) + '\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
