"""Two polynomial network passes: minimize F, then span over its entire face.

For authenticated primitive coherent surfaces in a knot exterior, and only
under that topological contract, the returned surface is connected. The
arithmetic API does not issue an UNKNOT verdict.
"""
from .model import Budget, noop
from .network import minimize_difference
from .checker import check_optimum


def optimum_face(edges, flows):
    arcs = []
    for (u, v, c, w), f in zip(edges, flows):
        if w == 0:
            continue
        if f < w:  # x <= 0 is necessary unless positive saturation.
            arcs.append((u, v, -c))
        if f > -w: # x >= 0 is necessary unless negative saturation.
            arcs.append((v, u, c))
    return tuple(arcs)


def span_network(model, face, initial):
    arcs, objective, p = list(face), [], list(initial)
    for t, (vs, hs) in enumerate(zip(model.vertices, model.heights)):
        upper, lower = model.n+2*t, model.n+2*t+1
        a = [h+initial[v] for v, h in zip(vs, hs)]
        p.extend((max(a), min(a)))
        objective.append((lower, upper, 0, 1))
        for v, h in zip(vs, hs):
            arcs.extend(((upper, v, -h), (v, lower, h)))
    return tuple(objective), tuple(arcs), p


def minimize_edge_then_span(model, *, max_work=None, check=noop):
    model.validate()
    b = Budget(max_work, check)
    first = minimize_difference(model.n, model.edges, (), model.initial, b.tick)
    face = optimum_face(model.edges, first['certificate']['edge_flows'])
    obj, arcs, initial = span_network(model, face, first['certificate']['potential'])
    second = minimize_difference(len(initial), obj, arcs, initial, b.tick)
    p = second['certificate']['potential'][:model.n]
    result = {'schema': 'edge-then-span-v1', 'potential': p,
              'edge_objective': model.objective(p), 'span': model.span(p),
              'score2': model.score2(p), 'first': first['certificate'],
              'second': second['certificate'],
              'stats': {'work': b.work,
                        'augmentations_first': first['stats']['augmentations'],
                        'augmentations_second': second['stats']['augmentations']}}
    if not replay_edge_then_span(model, result):
        raise ArithmeticError("independent two-stage optimum replay failed")
    return result


def replay_edge_then_span(model, answer):
    # Algebraic producer-independent certificate reconstruction is delegated to
    # the separate checker module (no call back into either network producer).
    from .checker import check_lexicographic
    return check_lexicographic(model, answer)
