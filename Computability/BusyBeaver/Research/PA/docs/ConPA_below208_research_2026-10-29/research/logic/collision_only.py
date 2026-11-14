"""Finite algebra certificate for the collision-only covering obstruction.

This does not decide first-order truth.  It checks all possible extensions of
one matrix in a fixed two-object structure.  Since every matrix/parameter
assignment has one of these extensions, the displayed mathematical argument
applies to every instance, without a truth predicate inside the model.
"""
import json

DOMAIN = (0, 1)  # empty e=0, nonempty u=1
EDGES = {(0, 1)}

def edge(x, y):
    return (x, y) in EDGES

def empty(x):
    return all(not edge(t, x) for t in DOMAIN)

def collision_cover(predicate, output):
    return all((not edge(x, output) or x in predicate)
               and (not (empty(x) and x in predicate) or edge(x, output))
               for x in DOMAIN)

def check():
    if not all(not edge(x, x) for x in DOMAIN):
        raise AssertionError('irreflexivity failed')
    records = []
    for mask in range(4):
        predicate = {x for x in DOMAIN if mask & (1 << x)}
        witness = 1 if 0 in predicate else 0
        if not collision_cover(predicate, witness):
            raise AssertionError((mask, witness))
        records.append({'matrix_extension': sorted(predicate), 'output': witness,
                        'all_collision_cover_clauses': True})
    # Full true-matrix covering at u fails in this same structure.
    def subset(x, a):
        return all(not edge(z, x) or edge(z, a) for z in DOMAIN)
    full_witnesses = [b for b in DOMAIN
                     if all(not subset(x, 1) or edge(x, b) for x in DOMAIN)]
    if full_witnesses:
        raise AssertionError('model unexpectedly has a full cover')
    return {'objects': ['e', 'u'], 'edges': [['e', 'u']], 'irreflexive': True,
            'predicates_checked': 4, 'records': records,
            'full_true_cover_at_u': False,
            'proof_status': 'finite extension check; unbounded schema result uses the accompanying finite-model soundness argument'}

if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
