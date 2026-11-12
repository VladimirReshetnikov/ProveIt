"""Untrusted producer for the atomic-transport eliminator-only R calculus.

The named R AST and elementary proof constructors are imported from the
attributed inherited_r.py. The new transformations are Q quotation,
structural transport elimination, structural identity expansion, zero-witness
boxing, and exact explicit-endpoint serialization. The measured checker
imports no producer and trusts only its final JSON certificate.
"""
from inherited_r import *


def pure_formula(f):
    tag = f[0]
    if tag == 'eq': return f
    if tag == 'q': return D(fresh('unused'), f[1], pure_formula(f[2]))
    if tag == 'd': return D(f[1], f[2], pure_formula(f[3]))
    raise ValueError('Not a formula: ' + repr(f))


def identity(f):
    """An explicit Eq/D identity proof; availability is major-only."""
    if f[0] == 'eq':
        _, s, t = f
        x = fresh('identity')
        return transport(hyp(f), x, Eq(s, V(x)), refl(s))
    if f[0] == 'd':
        _, x, y, body = f
        a, z = fresh('identity_witness'), fresh('identity_counter')
        opened = subst(body, x, V(a))
        clause = Q(y, opened)
        base = subst(opened, y, Z)
        step = qe(hyp(clause), S(V(z)), hyp(base))
        return de(hyp(f), a, di(f, V(a), z, step, False))
    raise ValueError('Identity targets must be Eq/D, not internal Q')


def atomic_transport(major, x, motive, minor):
    """Derive arbitrary Eq/D transport using only atomic primitive transport."""
    if motive[0] == 'eq':
        return transport(major, x, motive, minor)
    if motive[0] != 'd':
        raise ValueError('Translate Q before structural transport')
    _, s, t = major.goal
    _, w, y, body = motive
    a, z = fresh('transport_witness'), fresh('transport_counter')
    body_a = subst(body, w, V(a))
    source_clause = Q(y, subst(body_a, x, s))
    base_motive = subst(body_a, y, Z)
    target_base = subst(base_motive, x, t)
    source_base = atomic_transport(symmetry(major), x, base_motive, hyp(target_base))
    source_step = qe(hyp(source_clause), S(V(z)), source_base)
    step_motive = subst(body_a, y, S(V(z)))
    target_step = atomic_transport(major, x, step_motive, source_step)
    target = subst(motive, x, t)
    introduced = di(target, V(a), z, target_step, False)
    return de(minor, a, introduced)


def quote(clause):
    _, y, body = clause
    formula = D(fresh('unused'), y, body)
    z = fresh('quote_counter')
    return di(formula, S(Z), z,
              qe(hyp(clause), S(V(z)), hyp(subst(body, y, Z))), False)


def translate(proof, environment=()):
    """Translate full named Choice-DI/R proofs to atomic Eq/D proofs."""
    goal = pure_formula(proof.goal)
    if proof.rule == 'hyp':
        for source, provider in reversed(environment):
            if same(proof.goal, source): return provider
        return hyp(goal)
    if proof.rule == 'compute': return Proof(goal, 'compute')
    if proof.rule == 'transport':
        major, x, motive, minor = proof.data
        return atomic_transport(translate(major, environment), x,
                                pure_formula(motive), translate(minor, environment))
    if proof.rule == 'qe':
        major, target, base = proof.data
        out_major = translate(major, environment)
        _, x, y, body = out_major.goal
        a = fresh('specialization_witness')
        clause = Q(y, subst(body, x, V(a)))
        return de(out_major, a,
                  qe(hyp(clause), target, translate(base, environment)))
    if proof.rule == 'de':
        major, eigen, continuation = proof.data
        out_major = translate(major, environment)
        _, x, y, body = out_major.goal
        clause = Q(y, subst(body, x, V(eigen)))
        _, sx, sy, sb = major.goal
        source_clause = Q(sy, subst(sb, sx, V(eigen)))
        out_continuation = translate(continuation, environment + ((source_clause, quote(clause)),))
        return de(out_major, eigen, out_continuation)
    if proof.rule == 'di':
        witness, eigen, step, induction = proof.data
        _, x, y, body = proof.goal
        eta = V(eigen) if induction and body[0] == 'eq' else Z
        source_assumption = subst(subst(body, x, witness), y, eta)
        provider = hyp(pure_formula(source_assumption))
        out_step = translate(step, environment + ((source_assumption, provider),))
        return di(goal, witness, eigen, out_step, induction)
    raise ValueError(proof.rule)


def cut(proof, formula, replacement):
    """Untrusted finite proof substitution, with globally fresh named binders."""
    if proof.rule == 'hyp' and same(proof.goal, formula): return replacement
    def visit(item):
        if isinstance(item, Proof): return cut(item, formula, replacement)
        if isinstance(item, tuple): return tuple(visit(x) for x in item)
        return item
    return Proof(proof.goal, proof.rule, visit(proof.data))


def box_zero_introduction(proof):
    witness, eigen, step, induction = proof.data
    if witness != Z: return proof
    _, x, y, body = proof.goal
    box = W(S(Z))
    equation = computation(box)  # box = 0, with truthy raw box syntax
    eta = V(eigen) if induction and body[0] == 'eq' else Z
    base_motive = subst(body, y, eta)
    old_base = subst(base_motive, x, Z)
    new_base = subst(base_motive, x, box)
    replacement = atomic_transport(equation, x, base_motive, hyp(new_base))
    old_step = cut(step, old_base, replacement)
    step_motive = subst(body, y, S(V(eigen)))
    new_step = atomic_transport(symmetry(equation), x, step_motive, old_step)
    return di(proof.goal, box, eigen, new_step, induction)


def serialize(proof, *, permit_compound_transport=False):
    """Emit major-first depth-first packets in the exact runtime fresh order."""
    floor = 0
    counts = {'computation':0, 'atomic_transport':0, 'specialization':0,
              'paired_introduction':0, 'paired_elimination':0,
              'identity_expansion':0, 'available_major':0, 'zero_witness_box':0}

    def emit_major(p, rigid, context):
        if any(same(p.goal, f) for f in context):
            counts['available_major'] += 1
            return []
        return emit(p, rigid, context)

    def emit(p, rigid, context):
        nonlocal floor
        if p.rule == 'hyp':
            if not any(same(p.goal, f) for f in context):
                raise ValueError('Unbound hypothesis: ' + repr(p.goal))
            counts['identity_expansion'] += 1
            return emit(identity(p.goal), rigid, context)
        if p.rule == 'compute':
            counts['computation'] += 1
            return [[0, 0, 0, 0]]
        if p.rule == 'transport':
            major, x, motive, minor = p.data
            if not permit_compound_transport and motive[0] != 'eq':
                raise ValueError('Compound transport reached primitive serializer')
            counts['atomic_transport'] += 1
            _, s, u = major.goal
            cell = [encode(major.goal, rigid=rigid), encode(s, rigid=rigid),
                    encode(u, rigid=rigid), encode(motive, (x,), rigid)]
            return [cell] + emit_major(major, rigid, context) + emit(minor, rigid, context)
        if p.rule == 'qe':
            major, target, base = p.data
            if major.goal[0] != 'q': raise ValueError('Expected internal Q')
            counts['specialization'] += 1
            _, y, body = major.goal
            cell = [encode(major.goal, rigid=rigid), 0,
                    encode(target, rigid=rigid), encode(body, (y,), rigid)]
            return [cell] + emit_major(major, rigid, context) + emit(base, rigid, context)
        if p.rule == 'de':
            major, eigen, continuation = p.data
            counts['paired_elimination'] += 1
            cell = [encode(major.goal, rigid=rigid), 0, 0, []]
            cells = [cell] + emit_major(major, rigid, context)
            floor -= 1
            _, x, y, body = major.goal
            clause = Q(y, subst(body, x, V(eigen)))
            return cells + emit(continuation, {**rigid, eigen:floor}, context + [clause])
        if p.rule == 'di':
            witness, eigen, step, induction = p.data
            if witness == Z:
                counts['zero_witness_box'] += 1
                return emit(box_zero_introduction(p), rigid, context)
            counts['paired_introduction'] += 1
            cell = [0 if induction else [], 0, 0, encode(witness, rigid=rigid)]
            floor -= 1
            _, x, y, body = p.goal
            eta = V(eigen) if induction and body[0] == 'eq' else Z
            local = subst(subst(body, x, witness), y, eta)
            return [cell] + emit(step, {**rigid, eigen:floor}, context + [local])
        raise ValueError(p.rule)

    cells = emit(proof, {}, [])
    if free(proof.goal): raise ValueError('The public goal must be closed')
    return cells[::-1] + [encode(proof.goal)], counts


def produce(proof):
    return serialize(translate(proof))
