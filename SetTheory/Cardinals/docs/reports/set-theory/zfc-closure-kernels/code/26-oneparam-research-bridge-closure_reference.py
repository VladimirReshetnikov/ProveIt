#!/usr/bin/env python3
"""Finite-proof diagnostics for AU + one-parameter EPSC/XFP.

The default fixed axiom is observational adjunction AU, written with the short
formula U(y,b) := forall z (y in z -> b in z).  PairO remains a comparison preset.
The report proves the ordinary calibration: EPSC1 supplies O-singletons, which
give U=O; AU then gives PairO, enabling the full EPSC parameter-packing argument.
Those calibration proofs are not machine-checked by this reference program.

The program uses all 15 rules from finite_bridge.py, rejects equality atoms,
generates its own theory axioms, and gives a strict finite binary certificate
format. Bit 0 in an axiom descriptor means the selected fixed-axiom preset;
the preset is an explicit part of theory interpretation, not part of the word.

IMPORTANT IMPLEMENTATION SCOPE: this recursive Python implementation provides
finite diagnostics/reference calculations for an ideal primitive-recursive
syntax procedure. It is NOT an executable total infinite search: sufficiently
deep finite syntax may raise RecursionError. Such errors are never caught and
misreported as invalid proofs. The mathematical exhaustive-word semidecider
uses the ideal total syntax procedure. No binary TM or verified compiler is
claimed here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import finite_bridge as nd


class Templates:
    """Fresh named template binders, lowered once to de Bruijn syntax."""
    def __init__(self, matrix=None):
        self.matrix = matrix
        self.fresh_count = 0

    def fresh(self):
        self.fresh_count += 1
        return '@' + str(self.fresh_count)

    def quant(self, kind, fn):
        v = self.fresh()
        return (kind, v, fn(v))

    def all(self, fn): return self.quant('all', fn)
    def ex(self, fn): return self.quant('ex', fn)
    def mem(self, a, b): return ('mem', a, b)
    def imp(self, a, b): return ('imp', a, b)
    def both(self, a, b): return ('and', a, b)
    def either(self, a, b): return ('or', a, b)
    def neg(self, a): return self.imp(a, nd.BOT)
    def iff(self, a, b): return self.both(self.imp(a, b), self.imp(b, a))
    def empty(self, a): return self.all(lambda z: self.neg(self.mem(z, a)))
    def sub(self, a, b):
        return self.all(lambda z: self.imp(self.mem(z, a), self.mem(z, b)))
    def obs(self, a, b):
        return self.both(self.all(lambda z: self.iff(self.mem(z, a), self.mem(z, b))),
                         self.all(lambda z: self.iff(self.mem(a, z), self.mem(b, z))))
    def upper(self, y, b):
        return self.all(lambda z: self.imp(self.mem(y, z), self.mem(b, z)))
    def hole(self, x, y, p): return ('hole', x, y, p)

    def lower(self, tree, env=()):
        tag = tree[0]
        if tag == 'bot': return nd.BOT
        if tag == 'mem': return nd.Mem(env.index(tree[1]), env.index(tree[2]))
        if tag == 'hole':
            names = tree[1:]
            return nd.subst(self.matrix, lambda i: env.index(names[i]))
        if tag in ('and', 'or', 'imp'):
            return (tag, self.lower(tree[1], env), self.lower(tree[2], env))
        if tag in ('all', 'ex'):
            return (tag, self.lower(tree[2], (tree[1],) + env))
        raise ValueError('unknown template node')


def equality_free(p):
    if not nd.form_ok(p): return False
    todo = [p]
    while todo:
        q = todo.pop()
        if q[0] == 'eq': return False
        if q[0] in ('and', 'or', 'imp'): todo.extend(q[1:])
        elif q[0] in ('all', 'ex'): todo.append(q[1])
    return True


def pair_axiom():
    t = Templates()
    tree = t.all(lambda a: t.all(lambda b: t.ex(lambda c: t.all(lambda z:
        t.iff(t.mem(z, c), t.either(t.obs(z, a), t.obs(z, b)))))))
    return t.lower(tree)


def adjunction_axiom():
    """AU: forall a b exists c forall y (y in c iff (y in a or U(y,b)))."""
    t = Templates()
    tree = t.all(lambda a: t.all(lambda b: t.ex(lambda c: t.all(lambda y:
        t.iff(t.mem(y, c), t.either(t.mem(y, a), t.upper(y, b)))))))
    result = t.lower(tree)
    if not nd.bounded(result): raise AssertionError('adjunction template leaked a variable')
    return result


FIXED_AXIOMS = {'adjunction': adjunction_axiom, 'pair': pair_axiom}
VARIANTS = ('epsc', 'xfp')


def closure_axiom(matrix, variant='epsc'):
    if variant not in VARIANTS or not equality_free(matrix) or not nd.bounded(matrix, 3):
        raise ValueError('matrix must be equality-free with free indices below three')
    t = Templates(matrix)
    def at(p):
        sb = t.all(lambda x: t.ex(lambda b: t.all(lambda y:
            t.imp(t.hole(x, y, p), t.sub(y, b)))))
        def at_c(c):
            if variant == 'xfp':
                return t.all(lambda y: t.iff(t.mem(y, c), t.ex(lambda x:
                    t.both(t.either(t.empty(x), t.mem(x, c)), t.hole(x, y, p)))))
            cl = t.all(lambda x: t.all(lambda y: t.imp(
                t.both(t.either(t.empty(x), t.mem(x, c)), t.hole(x, y, p)), t.mem(y, c))))
            support = t.all(lambda y: t.imp(t.mem(y, c), t.ex(lambda x: t.hole(x, y, p))))
            return t.both(cl, support)
        return t.imp(sb, t.ex(at_c))
    result = t.lower(t.all(at))
    if not nd.bounded(result): raise AssertionError('template leaked a variable')
    return result


def axiom(witness, variant='epsc', fixed_axiom='adjunction'):
    if variant not in VARIANTS or fixed_axiom not in FIXED_AXIOMS:
        raise ValueError('unknown theory preset')
    kind, matrix = witness
    if kind == 'fixed' and matrix is None: return FIXED_AXIOMS[fixed_axiom]()
    if kind == 'closure': return closure_axiom(matrix, variant)
    raise ValueError('invalid axiom witness')


def check(axioms, nodes, goal=nd.BOT, variant='epsc', fixed_axiom='adjunction'):
    try:
        if variant not in VARIANTS or fixed_axiom not in FIXED_AXIOMS:
            return False
        context = tuple(axiom(w, variant, fixed_axiom) for w in axioms)
    except (ValueError, TypeError, IndexError):
        return False
    if not nd.check_nodes(nodes): return False
    if not all(equality_free(p) for n in nodes for p in (*n.context, n.conclusion)):
        return False
    return nodes[-1].context == context and nodes[-1].conclusion == goal


# A strict prefix codec. Gamma fields encode natural n as Elias gamma(n+1).
# Each finite word is tested once: word(n)=binary(n+1) with its leading 1 removed.
# The fixed theory and schema variant are supplied separately to check/refutation_word.
FORM_TAGS = ('bot', 'mem', 'imp', 'and', 'or', 'all', 'ex')

def field(n):
    if not nd.nat(n): raise ValueError('invalid natural field')
    b = bin(n + 1)[2:]
    return '0' * (len(b) - 1) + b

def encode_form(p):
    if not equality_free(p): raise ValueError('invalid equality-free formula')
    tag = p[0]
    text = format(FORM_TAGS.index(tag), '03b')
    if tag == 'mem': return text + field(p[1]) + field(p[2])
    if tag in ('imp', 'and', 'or'): return text + encode_form(p[1]) + encode_form(p[2])
    if tag in ('all', 'ex'): return text + encode_form(p[1])
    return text

class Malformed(ValueError): pass

class Reader:
    def __init__(self, bits): self.bits, self.i = bits, 0
    def take(self, n):
        if self.i + n > len(self.bits): raise Malformed('truncated field')
        out = self.bits[self.i:self.i+n]
        self.i += n
        return out
    def nat(self):
        zeros = 0
        while self.take(1) == '0': zeros += 1
        return int('1' + self.take(zeros), 2) - 1
    def count(self):
        n = self.nat()
        if n > len(self.bits) - self.i: raise Malformed('impossible record count')
        return n
    def form(self):
        tag_n = int(self.take(3), 2)
        if tag_n >= len(FORM_TAGS): raise Malformed('unused formula tag')
        tag = FORM_TAGS[tag_n]
        if tag == 'bot': return nd.BOT
        if tag == 'mem': return nd.Mem(self.nat(), self.nat())
        if tag in ('all', 'ex'): return (tag, self.form())
        return (tag, self.form(), self.form())


def encode(axioms, nodes):
    """Encode finite syntax. The fixed-axiom/schema presets are interpreted externally."""
    out = [field(len(axioms))]
    for kind, matrix in axioms:
        if kind == 'fixed' and matrix is None: out.append('0')
        elif kind == 'closure': out.extend(('1', encode_form(matrix)))
        else: raise ValueError('bad axiom descriptor')
    out.append(field(len(nodes)))
    rules = tuple(nd.ARITIES)
    for n in nodes:
        out.extend((field(rules.index(n.rule)), field(len(n.context))))
        out.extend(encode_form(p) for p in n.context)
        out.append(encode_form(n.conclusion))
        out.extend(field(i) for i in n.premises)
        if n.rule in ('AllE', 'ExI'): out.append(field(n.term))
    return ''.join(out)


def decode(bits):
    if not isinstance(bits, str) or any(b not in '01' for b in bits): return None
    r = Reader(bits)
    try:
        axioms = []
        for _ in range(r.count()):
            axioms.append(('fixed', None) if r.take(1) == '0' else ('closure', r.form()))
        nodes = []
        rules = tuple(nd.ARITIES)
        for _ in range(r.count()):
            rule_n = r.nat()
            if rule_n >= len(rules): raise Malformed('unused proof rule')
            rule = rules[rule_n]
            context = tuple(r.form() for _ in range(r.count()))
            conclusion = r.form()
            premises = tuple(r.nat() for _ in range(nd.ARITIES[rule]))
            term = r.nat() if rule in ('AllE', 'ExI') else None
            nodes.append(nd.Node(rule, context, conclusion, premises, term))
        if r.i != len(bits): raise Malformed('trailing bits')
        return tuple(axioms), tuple(nodes)
    except Malformed:
        return None


def refutation_word(bits, variant='epsc', fixed_axiom='adjunction'):
    certificate = decode(bits)
    return certificate is not None and check(*certificate, variant=variant, fixed_axiom=fixed_axiom)


def empty_certificate(variant='epsc', fixed_axiom='adjunction'):
    """An actual derivation of an empty object, not a contradiction."""
    axioms = (('closure', nd.BOT),)
    A = closure_axiom(nd.BOT, variant)
    ctx = (A,)
    nodes = []
    def add(rule, context, conclusion, premises=(), term=None):
        nodes.append(nd.Node(rule, context, conclusion, premises, term))
        return len(nodes)-1
    a0 = add('Ctx', ctx, A)
    instance = nd.inst(A[1], 0)
    a1 = add('AllE', ctx, instance, (a0,), 0)
    sb, exists_hull = instance[1:]
    # Prove forall x exists b forall y (Bottom -> Sub(y,b)).
    body_ex = sb[1]
    body_all = nd.inst(body_ex[1], 0)
    body_imp = body_all[1]
    c = (nd.BOT,) + ctx
    n0 = add('Ctx', c, nd.BOT)
    n1 = add('Exp', c, body_imp[2], (n0,))
    n2 = add('II', ctx, body_imp, (n1,))
    n3 = add('AllI', ctx, body_all, (n2,))
    n4 = add('ExI', ctx, body_ex, (n3,), 0)
    n5 = add('AllI', ctx, sb, (n4,))
    n6 = add('IE', ctx, exists_hull, (a1,n5))
    # Eliminate its hull witness, using its support clause to prove emptiness.
    H = exists_hull[1]
    hctx = (H,) + ctx
    shiftH = nd.shift(H)
    m = nd.Mem(0,1)
    actx = (m, shiftH) + ctx
    h0 = add('Ctx', actx, shiftH)
    if variant == 'epsc':
        support = shiftH[2]
        h1 = add('CE2', actx, support, (h0,))
        support_y = nd.inst(support[1],0)
        h2 = add('AllE', actx, support_y, (h1,),0)
    else:
        equivalence_y = nd.inst(shiftH[1],0)
        h1 = add('AllE', actx, equivalence_y, (h0,),0)
        support_y = equivalence_y[1]
        h2 = add('CE1', actx, support_y, (h1,))
    h3 = add('Ctx', actx, m)
    image = support_y[2]
    h4 = add('IE', actx, image, (h2,h3))
    inner = (image[1],) + tuple(map(nd.shift,actx))
    h5 = add('Ctx', inner, image[1])
    if variant == 'xfp':
        h5 = add('CE2', inner, nd.BOT, (h5,))
    h6 = add('ExE', actx, nd.BOT, (h4,h5))
    h7 = add('II', (shiftH,)+ctx, nd.Imp(m,nd.BOT), (h6,))
    h8 = add('AllI', hctx, nd.is_empty(0), (h7,))
    goal = nd.Ex(nd.is_empty(0))
    h9 = add('ExI', hctx, goal, (h8,),0)
    add('ExE',ctx,goal,(n6,h9))
    if not check(axioms,nodes,goal,variant,fixed_axiom):
        raise AssertionError('empty-object certificate rejected')
    return axioms, tuple(nodes), goal


def sat(p, rows, env=()):
    tag = p[0]
    if tag == 'bot': return False
    if tag == 'mem': return bool(rows[env[p[1]]] & (1 << env[p[2]]))
    if tag == 'imp': return not sat(p[1],rows,env) or sat(p[2],rows,env)
    if tag == 'and': return sat(p[1],rows,env) and sat(p[2],rows,env)
    if tag == 'or': return sat(p[1],rows,env) or sat(p[2],rows,env)
    vals = (sat(p[1],rows,(x,)+env) for x in range(len(rows)))
    return all(vals) if tag == 'all' else any(vals)


def semantic_template_checks():
    """Independent direct semantics detects binder/capture mistakes."""
    import itertools
    matrices = [nd.BOT, nd.Imp(nd.BOT,nd.BOT), nd.Mem(0,1), nd.Mem(1,2),
        nd.Imp(nd.Mem(2,0),nd.Mem(1,2)),
        nd.All(nd.Imp(nd.Mem(0,1),nd.Mem(0,3))),
        nd.Ex(nd.And(nd.Mem(0,2),nd.Mem(1,3)))]
    comparisons = {'adjunction': 0, 'pair': 0, 'epsc': 0, 'xfp': 0}
    for n in (1,2):
        for bits in range(1 << (n*n)):
            rows = [(bits >> (x*n)) & ((1<<n)-1) for x in range(n)]
            cols = [sum(bool(rows[x] & (1<<y)) << x for x in range(n)) for y in range(n)]
            empty = [c == 0 for c in cols]
            obs = lambda a,b: rows[a]==rows[b] and cols[a]==cols[b]
            upper = lambda y,b: rows[y] & ~rows[b] == 0
            adjunction_expected = all(any(all(
                bool(cols[c] & (1 << y)) == (bool(cols[a] & (1 << y)) or upper(y,b))
                for y in range(n)) for c in range(n))
                for a,b in itertools.product(range(n),repeat=2))
            if sat(adjunction_axiom(),rows) != adjunction_expected:
                raise AssertionError('AU binding failed')
            comparisons['adjunction'] += 1
            pair_expected = all(any(all(bool(cols[c] & (1<<y)) == (obs(y,a) or obs(y,b))
                                for y in range(n)) for c in range(n)) for a,b in itertools.product(range(n),repeat=2))
            if sat(pair_axiom(),rows) != pair_expected: raise AssertionError('PairO binding failed')
            comparisons['pair'] += 1
            for matrix in matrices:
                expected = {'epsc': True, 'xfp': True}
                for p in range(n):
                    rel = [[sat(matrix,rows,(x,y,p)) for y in range(n)] for x in range(n)]
                    bounded = all(any(all(not rel[x][y] or cols[y]&~cols[b]==0 for y in range(n))
                                      for b in range(n)) for x in range(n))
                    if not bounded: continue
                    good = {'epsc':False,'xfp':False}
                    for c in range(n):
                        image = [any((empty[x] or bool(cols[c]&(1<<x))) and rel[x][y]
                                     for x in range(n)) for y in range(n)]
                        closed = all(not image[y] or bool(cols[c]&(1<<y)) for y in range(n))
                        support = all(not(cols[c]&(1<<y)) or any(rel[x][y] for x in range(n)) for y in range(n))
                        good['epsc'] |= closed and support
                        good['xfp'] |= all(bool(cols[c]&(1<<y))==image[y] for y in range(n))
                    for variant in expected: expected[variant] &= good[variant]
                for variant in expected:
                    if sat(closure_axiom(matrix,variant),rows) != expected[variant]:
                        raise AssertionError('closure template binding failed')
                    comparisons[variant] += 1
    return comparisons


def self_test(variant='epsc', fixed_axiom='adjunction'):
    if variant not in VARIANTS or fixed_axiom not in FIXED_AXIOMS:
        raise ValueError('unknown theory preset')
    axioms,nodes,goal = empty_certificate(variant,fixed_axiom)
    bits = encode(axioms,nodes)
    if decode(bits)!=(axioms,nodes): raise AssertionError('certificate round trip failed')
    if refutation_word(bits,variant,fixed_axiom): raise AssertionError('noncontradiction called refutation')
    if decode(bits+'0') is not None or decode(bits[:-1]) is not None or decode(bits+'\n') is not None:
        raise AssertionError('strict framing failed')
    # Check equality-atom rejection and the unwanted fourth-free-slot restriction.
    bad_matrices = [nd.Eq(0,1),nd.Mem(0,3),nd.All(nd.Mem(0,4))]
    for matrix in bad_matrices:
        try: closure_axiom(matrix)
        except ValueError: pass
        else: raise AssertionError('bad matrix accepted')
    empty_metrics = {}
    for schema in VARIANTS:
        for fixed in FIXED_AXIOMS:
            for witness in (('fixed',None),('closure',nd.Mem(0,1)),('closure',nd.BOT)):
                a = axiom(witness,schema,fixed)
                proof = (nd.Node('Ctx',(a,),a),)
                if not check((witness,),proof,a,schema,fixed):
                    raise AssertionError('generated axiom rejected')
                word = encode((witness,),proof)
                if decode(word) != ((witness,),proof):
                    raise AssertionError('axiom certificate round trip failed')
            ea,en,eg = empty_certificate(schema,fixed)
            if not check(ea,en,eg,schema,fixed):
                raise AssertionError('variant empty-object proof rejected')
            if refutation_word(encode(ea,en),schema,fixed):
                raise AssertionError('variant empty-object proof called refutation')
            empty_metrics[schema] = {'nodes': len(en), 'bits': len(encode(ea,en))}
    au = adjunction_axiom()
    au_proof = (nd.Node('Ctx',(au,),au),)
    if check((('fixed',None),),au_proof,au,'epsc','pair'):
        raise AssertionError('AU certificate accepted as PairO fixed axiom')
    pair = pair_axiom()
    pair_proof = (nd.Node('Ctx',(pair,),pair),)
    if check((('fixed',None),),pair_proof,pair,'epsc','adjunction'):
        raise AssertionError('PairO certificate accepted as AU fixed axiom')
    peirce = nd.Imp(nd.Imp(nd.Imp(nd.BOT,nd.BOT),nd.BOT),nd.BOT)
    peirce_proof = (nd.Node('Pc',(),peirce),)
    if not check((),peirce_proof,peirce,'epsc','adjunction'):
        raise AssertionError('logical axiom rejected in a valid preset')
    if check((),peirce_proof,peirce,'epsc','unknown'):
        raise AssertionError('unknown theory preset accepted')
    prefix = 10000
    if any(refutation_word(bin(n+1)[3:],variant,fixed_axiom) for n in range(prefix)):
        raise AssertionError('unexpected refutation in diagnostic prefix')
    semantics = semantic_template_checks()
    matrix_samples = [nd.BOT,nd.Mem(0,1),nd.All(nd.Mem(0,3)),
                      nd.Imp(nd.Mem(0,2),nd.Mem(1,2))]
    for matrix in matrix_samples:
        if form_nodes(closure_axiom(matrix,'epsc')) != 3*form_nodes(matrix)+27:
            raise AssertionError('EPSC expanded-tree count disagrees with declared metric')
        if form_nodes(closure_axiom(matrix,'xfp')) != 3*form_nodes(matrix)+33:
            raise AssertionError('XFP expanded-tree count disagrees with declared metric')
    return dict(scope='recursive finite diagnostics/reference of an ideal PR syntax procedure; '
                      'not an executable total infinite search; no binary-machine or consistency proof',
                recursion_policy='deep finite syntax may raise RecursionError; '
                                 'recursion limits are not caught as invalid proofs',
                fixed_axiom=fixed_axiom,schema_variant=variant,
                certificate_theory_binding='fixed-axiom and schema presets are external to the word; '
                                           'descriptor bit 0 means the selected fixed axiom',
                kernel_rules=len(nd.ARITIES),empty_object_derivation_nodes=len(nodes),
                empty_object_certificate_bits=len(bits),empty_object_theorem_accepted=True,
                empty_object_is_refutation=False,strict_framing_checks=3,rejected_matrix_controls=3,
                empty_object_metrics_by_schema=empty_metrics,
                semantic_template_comparisons=sum(semantics.values()),
                semantic_template_comparisons_by_kind=semantics,
                finite_word_prefix=prefix,prefix_refutations=0,
                fixed_adjunction_formula_nodes=form_nodes(adjunction_axiom()),
                fixed_pair_formula_nodes=form_nodes(pair_axiom()),
                epsc_false_formula_nodes=form_nodes(closure_axiom(nd.BOT,'epsc')),
                xfp_false_formula_nodes=form_nodes(closure_axiom(nd.BOT,'xfp')),
                schema_expanded_tree_counts={'epsc':'3*matrix_nodes+27','xfp':'3*matrix_nodes+33'},
                node_metric='expanded primitive bot/mem/imp/and/or/all/ex tree nodes; '
                            'iff is expanded as two implications and a conjunction; '
                            'variable payloads excluded; this is neither bit length nor TM state count')


def form_nodes(p):
    if p[0] in ('bot','mem'): return 1
    return 1+sum(form_nodes(q) for q in p[1:])


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test',action='store_true')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--emit-empty-certificate',type=Path)
    ap.add_argument('--search-prefix',type=int)
    ap.add_argument('--variant',choices=VARIANTS,default='epsc')
    ap.add_argument('--fixed-axiom',choices=tuple(FIXED_AXIOMS),default='adjunction')
    args=ap.parse_args()
    if args.search_prefix is not None and args.search_prefix < 0:
        ap.error('--search-prefix must be nonnegative')
    if args.emit_empty_certificate:
        axioms,nodes,_=empty_certificate(args.variant,args.fixed_axiom)
        args.emit_empty_certificate.write_text(encode(axioms,nodes))
    if args.search_prefix is not None:
        for n in range(args.search_prefix):
            if refutation_word(bin(n+1)[3:],args.variant,args.fixed_axiom):
                print(json.dumps({'refutation_index':n,'variant':args.variant,
                                  'fixed_axiom':args.fixed_axiom,
                                  'scope':'finite diagnostic; recursive Python is not a total infinite search'}))
                return
        print(json.dumps({'searched':args.search_prefix,'refutations':0,'variant':args.variant,
                          'fixed_axiom':args.fixed_axiom,
                          'scope':'finite diagnostic; recursive Python is not a total infinite search'}))
    if args.self_test or args.search_prefix is None:
        text=json.dumps(self_test(args.variant,args.fixed_axiom),indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        print(text,end='')


if __name__=='__main__': main()
