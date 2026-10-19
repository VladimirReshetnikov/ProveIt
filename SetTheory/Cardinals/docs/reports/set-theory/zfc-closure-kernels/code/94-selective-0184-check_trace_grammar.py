#!/usr/bin/env python3
"""Independently check a frozen trace grammar and its abstract entry interface.

This certifies trace-word equalities, terminal orientations, all routed
projections, bootstrap projections and source-tree depth/zero bounds. It does
not certify the physical binary machine or a new working-state bound.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'theory_work'))
from trace_commutation import TraceNormalizer


def check(reference, candidate, strict=False):
    inp = reference / 'inputs'
    source = json.loads((inp / 'closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((inp / 'semantic-symbols.json').read_text())
    tr = TraceNormalizer(source, symbols, strict=strict)
    nf = tr.normalize
    data = json.loads(candidate.read_text())
    lines = (inp / 'state_reduction/route-grammar.txt').read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    old, names = {}, {}
    for line in lines[1:n+1]:
        split, word, state = line.split()
        split, state = int(split), int(state)
        key = nf(word)
        assert key not in old
        old[key] = nf(word[:split]), nf(word[split:])
        names[state] = key
    expected_roots = {nf(w) for w in lines[n+1:n+1+nr]}
    allowed = {c: int(m) for c,m in map(str.split, lines[n+1+nr:])}
    assert len(allowed) == na == len(symbols)
    rules = {w: (a,b) for w,a,b in data['rules']}
    assert len(rules) == len(data['rules']) == data['rules_count']
    swaps = 0
    for w,(a,b) in rules.items():
        assert len(w) > 1 and nf(w) == w == nf(a+b)
        assert len(w) == len(a) + len(b)
        certificate = tr.certificate(a+b)
        assert certificate['after'] == w
        swaps += len(certificate['adjacent_swaps'])
        for bit, child in enumerate((a,b)):
            if len(child) == 1:
                assert allowed[child] & (1 << bit)
            else:
                assert child in rules

    def project(w, prefix):
        for bit in prefix:
            assert w in rules
            w = rules[w][int(bit)]
        return w

    tokens = iter((inp / 'state_reduction/route-constraints.txt').read_text().split())
    ng = int(next(tokens))
    routes = {(r['source'],r['read']):r['word'] for r in data['routes']}
    assert len(routes) == ng == len(data['routes'])
    projection_count = 0
    expected_route_keys = set()
    for _ in range(ng):
        state, bit = int(next(tokens)), int(next(tokens))
        old_root = next(tokens)
        nc = int(next(tokens))
        expected_route_keys.add((state,bit))
        root = routes[state,bit]
        assert root in rules
        for _ in range(nc):
            prefix, target = next(tokens), next(tokens)
            assert project(root,prefix) == nf(target)
            projection_count += 1
    assert set(routes) == expected_route_keys
    # Remaining expression metadata is checked through the independent AST
    # reconstruction below instead of trusting the searcher's expression file.
    lock_lines = (inp / 'state_reduction/bootstrap-lock54.txt').read_text().splitlines()
    lock_count = int(lock_lines[0])
    assert len(lock_lines) == lock_count + 1
    for line in lock_lines[1:]:
        w, bit, target = line.split()
        w = nf(w)
        expected_roots.add(w)
        assert project(w,bit) == nf(target)
    assert set(data['roots']) == expected_roots

    by_ast = {int(ast): names[int(q)] for q,ast in source['sequence_ast_roots'].items()}
    def join(a,b):
        return 1+a[0], max(1+a[0],a[1],b[1]), 1+max(a[2],b[2])
    visiting = set()
    @lru_cache(None)
    def astprop(i):
        key=('ast',i)
        assert key not in visiting
        visiting.add(key)
        if i in by_ast:
            ans = wordprop(by_ast[i])
        else:
            row=source['ast_dag'][i]
            ans = (0,0,0) if row[0]=='L' else join(astprop(row[1]),astprop(row[2]))
        visiting.remove(key)
        return ans
    @lru_cache(None)
    def wordprop(w):
        key=('word',w)
        assert key not in visiting
        visiting.add(key)
        if len(w)==1:
            ans=astprop(source['atoms'][symbols[w]]['ast'])
        else:
            a,b=rules[w] if w in rules else old[w]
            ans=join(wordprop(a),wordprop(b))
        visiting.remove(key)
        return ans
    properties=astprop(source['original_ast'])
    assert list(properties)==data['properties']
    assert properties[1]<=6 and properties[2]<=64
    reached=set()
    def visit(w):
        if len(w)==1 or w in reached:return
        reached.add(w)
        for child in rules[w]:visit(child)
    for root in expected_roots | set(routes.values()):visit(root)
    assert reached==set(rules)
    return {'status':'PASS_ABSTRACT_TRACE_GRAMMAR','rules':len(rules),
            'trace_criterion':'strict_disjoint' if strict else 'additive_outputs',
            'trace_equation_swap_witnesses':swaps,'entry_projections':projection_count,
            'bootstrap_projections':lock_count,'source_properties':list(properties),
            'candidate_sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),
            'scope':'Source trace identities and abstract entry constraints only; no binary-table or blank-start theorem.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('candidate',type=Path)
    p.add_argument('--reference',type=Path,default=ROOT/'packages/zfc245-proof-20261018')
    p.add_argument('--strict',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=check(a.reference,a.candidate,a.strict)
    encoded=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(encoded)
    print(encoded)

if __name__=='__main__':main()
