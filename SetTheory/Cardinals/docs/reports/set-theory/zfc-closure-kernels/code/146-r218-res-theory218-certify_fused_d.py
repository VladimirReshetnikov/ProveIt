#!/usr/bin/env python3
"""Explicit K,S,Peirce/MP certificate for D iff T plus explosion.

The inherited CD230.v derives these three implicational schemes from rho8
alone.  The verifier below performs only finite structural equality checks;
it does not use Boolean truth tables, unification, or proof search.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

ROOT = Path(__file__).parent
CERTIFICATE = ROOT / 'fused_d_equivalence_certificate.json'


def I(a, b):
    return a, b


def term(t):
    return tuple(map(term, t)) if isinstance(t, list) else t


def axiom(rule, parameters):
    if rule == 'K':
        a, b = parameters
        return I(a, I(b, a))
    if rule == 'S':
        a, b, c = parameters
        return I(I(a, I(b, c)), I(I(a, b), I(a, c)))
    if rule == 'P':
        a, b = parameters
        return I(I(I(a, b), a), a)
    raise ValueError(rule)


def build():
    nodes = []
    def add(formula, rule, support=(), **other):
        nodes.append(dict(formula=formula, rule=rule, support=frozenset(support), **other))
        return len(nodes) - 1
    def hyp(formula):
        index = len(nodes)
        return add(formula, 'hyp', [index])
    @lru_cache(None)
    def ax(rule, parameters):
        return add(axiom(rule, parameters), rule, parameters=parameters)
    @lru_cache(None)
    def mp(major, minor):
        fm, fn = nodes[major]['formula'], nodes[minor]['formula']
        assert isinstance(fm, tuple) and fm[0] == fn
        return add(fm[1], 'MP', nodes[major]['support'] | nodes[minor]['support'],
                   major=major, minor=minor)
    @lru_cache(None)
    def identity(formula):
        return mp(mp(ax('S', (formula, I(formula, formula), formula)),
                     ax('K', (formula, I(formula, formula)))),
                  ax('K', (formula, formula)))
    @lru_cache(None)
    def deduce(index, assumption):
        formula, h = nodes[index]['formula'], nodes[assumption]['formula']
        assert nodes[assumption]['rule'] == 'hyp'
        if assumption not in nodes[index]['support']:
            return mp(ax('K', (formula, h)), index)
        if index == assumption:
            return identity(h)
        assert nodes[index]['rule'] == 'MP'
        major, minor = nodes[index]['major'], nodes[index]['minor']
        y = nodes[minor]['formula']
        return mp(mp(ax('S', (h, y, formula)), deduce(major, assumption)),
                  deduce(minor, assumption))

    p, a, f = 'P', 'A', 'F'
    pf, pa, fa = I(p, f), I(p, a), I(f, a)
    nnp = I(pf, f)
    d = I(nnp, a)

    hd, hp, hpf = hyp(d), hyp(p), hyp(pf)
    nnp_from_p = deduce(mp(hpf, hp), hpf)
    first = deduce(deduce(mp(hd, nnp_from_p), hp), hd)

    hd, hf, hpf = hyp(d), hyp(f), hyp(pf)
    nnp_from_f = deduce(hf, hpf)
    second = deduce(deduce(mp(hd, nnp_from_f), hf), hd)

    hpa, hfa, hnnp = hyp(pa), hyp(fa), hyp(nnp)
    haf, hp = hyp(I(a, f)), hyp(p)
    pf_from_af = deduce(mp(haf, mp(hpa, hp)), hp)
    a_from_af = mp(hfa, mp(hnnp, pf_from_af))
    peirce_minor = deduce(a_from_af, haf)
    conclusion = mp(ax('P', (a, f)), peirce_minor)
    third = deduce(deduce(deduce(conclusion, hnnp), hfa), hpa)
    roots = dict(D_implies_T=first, D_implies_EXP=second, T_EXP_implies_D=third)
    assert all(not nodes[index]['support'] for index in roots.values())

    live = set()
    def visit(index):
        if index in live:
            return
        node = nodes[index]
        assert node['rule'] != 'hyp'
        if node['rule'] == 'MP':
            visit(node['major'])
            visit(node['minor'])
        live.add(index)
    for index in roots.values():
        visit(index)
    remap = {old: new for new, old in enumerate(sorted(live))}
    proof = []
    for old in sorted(live):
        node = {k: v for k, v in nodes[old].items() if k != 'support'}
        if node['rule'] == 'MP':
            node.update(major=remap[node['major']], minor=remap[node['minor']])
        proof.append(node)
    return dict(scope='Pure implication, with F an arbitrary formula parameter.',
                inherited_basis='CD230.v: thm_K, thm_S, thm_P, each derived from rho8 alone.',
                nodes=proof, roots={name: remap[index] for name, index in roots.items()})


def verify(certificate):
    nodes = certificate['nodes']
    for index, node in enumerate(nodes):
        formula, rule = term(node['formula']), node['rule']
        if rule in ('K', 'S', 'P'):
            assert formula == axiom(rule, term(node['parameters']))
        else:
            assert rule == 'MP'
            major, minor = node['major'], node['minor']
            assert 0 <= major < index and 0 <= minor < index
            implication, premise = term(nodes[major]['formula']), term(nodes[minor]['formula'])
            assert isinstance(implication, tuple)
            assert implication == I(premise, formula)
    p, a, f = 'P', 'A', 'F'
    d = I(I(I(p, f), f), a)
    wanted = dict(D_implies_T=I(d, I(p, a)), D_implies_EXP=I(d, I(f, a)),
                  T_EXP_implies_D=I(I(p, a), I(I(f, a), d)))
    for name, formula in wanted.items():
        assert term(nodes[certificate['roots'][name]]['formula']) == formula
    return dict(status='PASS', nodes=len(nodes),
                modus_ponens_steps=sum(node['rule'] == 'MP' for node in nodes),
                axiom_instances=sum(node['rule'] != 'MP' for node in nodes),
                roots=certificate['roots'],
                conclusion='D and T+EXP have the same theorem set over the retained rho8 calculus.',
                limitation='No Con(ZFC) calibration of this altered quantifier calculus is asserted.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--verify-only', action='store_true')
    options = parser.parse_args()
    if options.verify_only:
        result = verify(json.loads(CERTIFICATE.read_text()))
    else:
        certificate = build()
        result = verify(certificate)
        CERTIFICATE.write_text(json.dumps(certificate, indent=2) + '\n')
        (ROOT / 'fused_d_equivalence_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
