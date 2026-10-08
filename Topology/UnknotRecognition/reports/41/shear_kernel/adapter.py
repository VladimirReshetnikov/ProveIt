"""Opt-in WordArena bridge for the inspected ProveIt API.

No monkey patch, no change to recognizer defaults, and no knot verdict.
``prepare_step`` reads the original arena but does not mutate its roots.
``install_prepared`` is for a NEW atomic-shear certificate protocol only.
Its roots are cyclic rotations, not necessarily the literal representatives
produced by existing replay. For legacy certificates use ``replay_in_arena``.
Caller is responsible for a whole-operation deadline and integration replay.
"""
from __future__ import annotations
from .slp import Grammar
from .optimize import optimize,verify_optimization,replay_moves

def import_arena(arena, roots):
    g=Grammar(); mapping={0:0}
    for node in arena._reachable(roots):
        arena.tick(); rule=arena.rules[node]
        if rule[0]=='t': mapping[node]=g.letter(rule[1])
        elif rule[0]=='c': mapping[node]=g.concat(mapping[rule[1]],mapping[rule[2]])
        else: raise ValueError('unsupported WordArena rule')
    rs=[mapping[r] for r in roots]; g.validate_roots(rs)
    return g,rs

def prepare_step(arena, roots, alive, **kwargs):
    g,rs=import_arena(arena,roots)
    result=optimize(g,rs,sorted(alive),**kwargs)
    verify_optimization(g,rs,result.certificate)
    return result,replay_moves(result.certificate)

def install_prepared(arena,result):
    """Direct import for a new atomic protocol, NOT legacy positional replay."""
    g=result.grammar; rs=result.roots; mapping={0:0}
    for n in g.reachable(rs):
        arena.tick(); q=g.rules[n]
        if q[0]=='t': mapping[n]=arena.letter(q[1])
        elif q[0]=='c': mapping[n]=arena.concat(mapping[q[1]],mapping[q[2]])
        elif q[0]=='p': mapping[n]=arena.power(mapping[q[1]],q[2])
        else: raise ValueError('unsupported output rule')
    new=[mapping[r] for r in rs]
    if sum(arena.lengths[x] for x in new)!=result.certificate['optimal_length']:
        raise ArithmeticError('WordArena output-length discrepancy')
    return new


def replay_in_arena(arena,roots,alive,result):
    """Legacy-compatible installation through the existing literal move schema.

    This deliberately uses generic host reduction and therefore does NOT inherit
    the direct-constructor rule-growth theorem. Returned roots and moves must be
    committed together only after successful completion and independent replay.
    """
    new=list(roots); moves=replay_moves(result.certificate)
    for move in moves:
        a=move['multiplier']; subset=set(move['subset']); k=move.get('exponent',1)
        positive=arena.power(arena.letter(a),k); negative=arena.inverse(positive)
        images={}
        for generator in alive:
            x=arena.letter(generator)
            if generator!=abs(a):
                if -generator in subset: x=arena.concat(negative,x)
                if generator in subset: x=arena.concat(x,positive)
            images[generator]=x; images[-generator]=arena.inverse(x)
        new=[arena.cyclic_reduce(x) for x in arena.substitute(new,images)]
    if sum(arena.lengths[x] for x in new)!=result.certificate['optimal_length']:
        raise ArithmeticError('legacy replay length mismatch')
    return new,moves
