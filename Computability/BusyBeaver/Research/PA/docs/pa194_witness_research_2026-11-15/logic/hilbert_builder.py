#!/usr/bin/env python3
"""Produce universal Hilbert proof templates for an independent witness consequent.

The independently replayable certificates use K, S and Peirce as derived rules
of the UNCHANGED restricted rho8 basis. They do not use a truth-table oracle.
They are finite syntactic certificates, not proof-assistant kernel theorems.
"""
from pathlib import Path
import argparse, json


class Builder:
    def __init__(self):
        self.terms = []
        self.term_index = {}
        self.proofs = []

    def term(self, *node):
        if node not in self.term_index:
            self.term_index[node] = len(self.terms)
            self.terms.append(list(node))
        return self.term_index[node]

    def i(self, a, b): return self.term('I', a, b)
    def u(self, d, a): return self.term('U', d, a)
    def e(self, a, b): return self.term('E', a, b)
    def n(self, a): return self.i(a, self.term('nat', 1))

    def add(self, rule, args, out):
        self.proofs.append(dict(rule=rule, args=list(args), conclusion=out))
        return len(self.proofs) - 1

    def out(self, p): return self.proofs[p]['conclusion']

    def k(self, a, b): return self.add('K', (a, b), self.i(a, self.i(b, a)))
    def s(self, a, b, c):
        return self.add('S', (a, b, c), self.i(self.i(a, self.i(b, c)), self.i(self.i(a, b), self.i(a, c))))
    def peirce(self, a, b):
        return self.add('Peirce', (a, b), self.i(self.i(self.i(a, b), a), a))
    def mp(self, major, minor):
        form = self.terms[self.out(major)]
        assert form[0] == 'I' and form[1] == self.out(minor), ('mp', major, minor)
        return self.add('MP', (major, minor), form[2])
    def gen(self, d, p): return self.add('Gen', (d, p), self.u(d, self.out(p)))
    def gamma(self, a): return self.add('Gamma', (a,), self.i(a, self.u(a, a)))
    def h6(self, d, a, h):
        return self.add('h6Q', (d, a, h), self.i(self.u(d, self.i(a, h)), self.i(self.u(d, a), self.u(d, h))))
    def w(self, d, h): return self.u(d, self.n(self.e(h, d)))
    def h5(self, d, h): return self.add('h5', (d, h), self.n(self.w(d, h)))
    def h5x(self, d, a, h): return self.add('h5X', (d, a, h), self.i(self.w(d, h), a))
    def quant_x(self, d, h): return self.u(d, self.n(self.u(d, h)))
    def h1(self, d, h): return self.add('h1', (d, h), self.i(self.n(self.quant_x(d, h)), h))
    def dual_b(self, d, h): return self.add('dualB', (d, h), self.i(self.n(h), self.quant_x(d, h)))
    def hyp(self, a): return self.add('Assumption', (a,), a)

    def compose(self, p, q):
        """Compose proofs of A -> B and B -> C, without hypotheses."""
        _, a, b = self.terms[self.out(p)]
        _, bb, c = self.terms[self.out(q)]
        assert b == bb
        lift = self.mp(self.k(self.out(q), a), q)
        return self.mp(self.mp(self.s(a, b, c), lift), p)

    def identity(self, a):
        aa = self.i(a, a)
        return self.mp(self.mp(self.s(a, aa, a), self.k(a, aa)), self.k(a, a))

    def deduct(self, hypothesis, p):
        memo = {}
        def go(j):
            if j in memo: return memo[j]
            row = self.proofs[j]
            if row['rule'] == 'Assumption' and row['conclusion'] == hypothesis:
                result = self.identity(hypothesis)
            elif row['rule'] == 'MP':
                major, minor = row['args']
                a, b = self.out(minor), row['conclusion']
                result = self.mp(self.mp(self.s(hypothesis, a, b), go(major)), go(minor))
            else:
                # No generalization over a dependent assumption is used.
                assert row['rule'] != 'Gen' or not self.assumptions(j)
                result = self.mp(self.k(row['conclusion'], hypothesis), j)
            memo[j] = result
            return result
        return go(p)

    def assumptions(self, p):
        row = self.proofs[p]
        if row['rule'] == 'Assumption': return {row['conclusion']}
        if row['rule'] == 'MP':
            return self.assumptions(row['args'][0]) | self.assumptions(row['args'][1])
        if row['rule'] == 'Gen': return self.assumptions(row['args'][1])
        return set()

    def old_explosion(self, a):
        z, f = self.term('nat', 0), self.term('nat', 1)
        return self.compose(self.k(f, self.quant_x(z, a)), self.h1(z, a))

    def witness_explosion(self, a):
        z, f = self.term('nat', 0), self.term('nat', 1)
        ee = self.e(z, f)
        implication = self.i(ee, f)
        lifted_k = self.gen(f, self.k(f, ee))
        modal = self.mp(self.h6(f, f, implication), lifted_k)
        to_witness = self.compose(self.gamma(f), modal)
        return self.compose(to_witness, self.h5x(f, a, z))

    def dump(self, p, title, destination):
        assert not self.assumptions(p)
        needed = set()
        def visit(j):
            if j in needed: return
            needed.add(j)
            row = self.proofs[j]
            if row['rule'] == 'MP':
                for q in row['args']: visit(q)
            elif row['rule'] == 'Gen': visit(row['args'][1])
        visit(p)
        mapping = {old: new for new, old in enumerate(sorted(needed))}
        proofs = []
        for old in sorted(needed):
            row = dict(self.proofs[old]); args = row['args'][:]
            if row['rule'] == 'MP': args = [mapping[j] for j in args]
            if row['rule'] == 'Gen': args[1] = mapping[args[1]]
            row['args'] = args; proofs.append(row)
        obj = dict(format='universal-hilbert-template-v1', title=title,
                   terms=self.terms, proofs=proofs, final=mapping[p],
                   term_interpretation={'I':'4 * Cantor(a,b)', 'U':'4 * Cantor(body,binder) + 2', 'E':'4 * Cantor(a,b) + 3'},
                   retained_lemmas=['K', 'S', 'Peirce: derived uniformly from unchanged restricted rho8'],
                   proof_assistant_kernel_checked=False)
        destination.write_text(json.dumps(obj, separators=(',', ':')) + '\n')
        return dict(file=destination.name, steps=len(proofs), rules=sorted(set(row['rule'] for row in proofs)), final_formula=self.out(p))


def build(output):
    output.mkdir(parents=True, exist_ok=True)
    receipts = []
    b = Builder(); d = b.term('parameter', 'D'); h = b.term('parameter', 'H'); a = b.term('parameter', 'A')
    old_to_new = b.compose(b.h5(d, h), b.old_explosion(a))
    receipts.append(b.dump(old_to_new, 'Old calculus derives independent-consequent witness', output / 'old_to_h5X.json'))
    b = Builder(); d = b.term('parameter', 'D'); h = b.term('parameter', 'H'); f = b.term('nat', 1)
    receipts.append(b.dump(b.h5x(d, f, h), 'New witness recovers the old witness at A=1', output / 'h5X_to_old.json'))
    b = Builder(); a = b.term('parameter', 'A')
    receipts.append(b.dump(b.witness_explosion(a), 'New witness supplies explosion without h1', output / 'h5X_explosion.json'))
    b = Builder(); d = b.term('parameter', 'D'); h = b.term('parameter', 'H'); f = b.term('nat', 1)
    x = b.quant_x(d, h); nx = b.n(x); nh = b.n(h)
    px, ph = b.hyp(nx), b.hyp(nh)
    contradiction = b.mp(px, b.mp(b.dual_b(d, h), ph))
    hh = b.mp(b.witness_explosion(h), contradiction)
    nh_h = b.deduct(nh, hh)
    hh = b.mp(b.peirce(h, f), nh_h)
    old_head = b.deduct(nx, hh)
    receipts.append(b.dump(old_head, 'Dual B plus new witness recovers original h1', output / 'coupled_to_h1.json'))
    b = Builder(); d = b.term('parameter', 'D'); h = b.term('parameter', 'H'); f = b.term('nat', 1)
    x = b.quant_x(d, h); nx = b.n(x); nh = b.n(h)
    ph, px = b.hyp(nh), b.hyp(nx)
    ff = b.mp(ph, b.mp(b.h1(d, h), px))
    xx = b.mp(b.old_explosion(x), ff)
    nx_x = b.deduct(nx, xx)
    xx = b.mp(b.peirce(x, f), nx_x)
    new_head = b.deduct(nh, xx)
    receipts.append(b.dump(new_head, 'Original h1 derives dual B', output / 'h1_to_dualB.json'))
    (output / 'generation.json').write_text(json.dumps(receipts, indent=2) + '\n')
    print(json.dumps(receipts, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    build(parser.parse_args().output)
