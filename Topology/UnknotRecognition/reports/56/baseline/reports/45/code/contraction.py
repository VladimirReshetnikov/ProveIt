"""Normalization-free parallel primitive-power contraction prototype.

The output is conditional algebraic evidence for a TORSION-FREE input group,
not a knot verdict. A caller must establish this hypothesis from geometry.
No call to free reduction, word equality, or expansion occurs in this module.
"""
from christoffel import Arena, InputError, ResourceLimit, classify
from checker import verify_power


class GenericArena(Arena):
    def letter(self, x):
        if type(x) is not int or not x:
            raise InputError('nonzero integer letter required')
        return self._put(('t', x), 1)


def metadata(rules):
    """At most three support labels are retained: three means ineligible."""
    if not rules or rules[0] is not None: raise InputError('bad empty node')
    result = [(frozenset(), 0, 0, True, 0)]
    for n, rule in enumerate(rules[1:], 1):
        if len(rule) == 2 and rule[0] == 't':
            x = rule[1]
            if type(x) is not int or not x: raise InputError('bad letter')
            result.append((frozenset([abs(x)]), x, x, True, 1))
        elif len(rule) == 3 and rule[0] == 'c':
            if not all(type(x) is int and 0 <= x < n for x in rule[1:]): raise InputError('bad DAG')
            s, a, b, ok, l = result[rule[1]]
            t, c, d, good, m = result[rule[2]]
            support = frozenset(sorted(s | t)[:3])
            result.append((support, a or c, d or b,
                           ok and good and (not l or not m or b != -c), l+m))
        else: raise InputError('bad rule')
    return result


def extract_pair(rules, root, pair):
    names = sorted(pair)
    rename = {names[0]: 1, -names[0]: -1, names[1]: 2, -names[1]: -2}
    seen, stack = set(), [root]
    while stack:
        i = stack.pop()
        if i == 0 or i in seen: continue
        seen.add(i)
        if rules[i][0] == 'c': stack.extend(rules[i][1:])
    small, mapping = [None], {0: 0}
    for i in sorted(seen):
        r = rules[i]
        s = ('t', rename[r[1]]) if r[0] == 't' else ('c', mapping[r[1]], mapping[r[2]])
        mapping[i] = len(small); small.append(s)
    return small, mapping[root]


def plan_round(rules, roots, alive):
    """Deterministic greedy disjoint pairing; NOT an optimal schedule search."""
    meta = metadata(rules)
    used, selected = set(), []
    for slot, root in enumerate(roots):
        support, first, last, reduced, size = meta[root]
        if (len(support) != 2 or not support <= set(alive) or support & used
            or not size or not reduced or first == -last): continue
        small, r = extract_pair(rules, root, support)
        answer = classify(small, r)
        if answer.certificate:
            selected.append(dict(slot=slot, pair=sorted(support)))
            used.update(support)
    return selected


def apply_round(rules, roots, alive, selected, *, max_nodes=1_000_000, max_bits=100_000):
    """Replay each local width certificate; substitute a->t^v,b->t^-u.

    Relator slots are retained. The selected donors are discharged as freely
    trivial after projection, which follows from the checked kernel theorem.
    Other relators are left as raw substitution circuits, without cancellation.
    """
    if len(rules) > max_nodes: raise ResourceLimit('contraction node cap')
    meta = metadata(rules)
    if max(x[4].bit_length() for x in meta) > max_bits:
        raise ResourceLimit('contraction bit cap')
    used, verified = set(), []
    for item in selected:
        if type(item) is not dict or set(item) != {'slot', 'pair'}: raise InputError('bad round item')
        slot, pair = item['slot'], item['pair']
        if type(slot) is not int or not 0 <= slot < len(roots): raise InputError('bad slot')
        if (not isinstance(pair, list) or len(pair) != 2 or
            any(type(x) is not int for x in pair) or pair != sorted(set(pair))
            or not set(pair) <= set(alive) or used.intersection(pair)): raise InputError('bad/disjoint pair')
        small, r = extract_pair(rules, roots[slot], pair)
        ans = classify(small, r)
        c = ans.certificate
        if c is None or not verify_power(small, c): raise InputError('not a verified primitive power')
        verified.append((slot, pair, c.u, c.v, c.exponent))
        used.update(pair)
    new = GenericArena()
    images = {}
    survivors = set(alive)
    for g in alive:
        images[g], images[-g] = new.letter(g), new.letter(-g)
    for slot, (a, b), u, v, d in verified:
        for old, exponent in ((a, v), (b, -u)):
            pos = new.letter(a if exponent >= 0 else -a)
            neg = new.letter(-a if exponent >= 0 else a)
            images[old] = new.power(pos, abs(exponent))
            images[-old] = new.power(neg, abs(exponent))
        survivors.remove(b)
    reachable, stack = set(), list(roots)
    while stack:
        i = stack.pop()
        if not i or i in reachable: continue
        reachable.add(i)
        if rules[i][0] == 'c': stack.extend(rules[i][1:])
    translation = [0]*len(rules)
    for i in range(1, len(rules)):
        if i not in reachable: continue
        r = rules[i]
        translation[i] = images[r[1]] if r[0] == 't' else new.concat(translation[r[1]], translation[r[2]])
        if len(new.rules) > max_nodes: raise ResourceLimit('contraction node cap')
        if new.lengths[translation[i]].bit_length() > max_bits: raise ResourceLimit('contraction bit cap')
    new_roots = [translation[r] for r in roots]
    for slot, *_ in verified: new_roots[slot] = 0
    return new, new_roots, survivors, verified


def run_contractions(rules, roots, alive, *, max_rounds=100, max_nodes=1_000_000,
                     max_bits=100_000):
    records = []
    for _ in range(max_rounds):
        if len(alive) <= 1: break
        selected = plan_round(rules, roots, alive)
        if not selected: break
        new, roots, alive, verified = apply_round(rules, roots, alive, selected,
                            max_nodes=max_nodes, max_bits=max_bits)
        records.append(dict(selected=selected, rank=len(alive), nodes=len(new.rules),
                            length_bits=max(new.lengths).bit_length()))
        rules = new.rules
    return dict(status='CONDITIONAL_TORSION_FREE_CONTRACTION', rules=rules,
                roots=roots, alive=sorted(alive), rounds=records)


def balanced_family(depth, exponent_bits=16):
    """Abstract presentations of Z, NOT manufactured knot-diagram claims.

    Each edge has two relators (a^N b)^2 and (a^N b)^3. Their normal closure
    contains a^N b without torsion assumptions. The left representative stays
    unchanged under projection. Bottom-up slot order yields depth rounds.
    """
    A = GenericArena()
    rank = 2**depth
    current = list(range(1, rank+1)); roots = []
    for _ in range(depth):
        next_level = []
        for a, b in zip(current[::2], current[1::2]):
            w = A.concat(A.power(A.letter(a), 2**exponent_bits), A.letter(b))
            roots += [A.power(w, 2), A.power(w, 3)]
            next_level.append(a)
        current = next_level
    return A, roots, set(range(1, rank+1))


def rank_one_endpoint(rules, roots, alive):
    """Check that a one-generator endpoint presents Z, with no normalization.

    This does not discharge the torsion-free hypotheses of preceding rounds.
    """
    if len(alive) != 1: return False
    g = next(iter(alive))
    reachable, stack = set(), list(roots)
    while stack:
        i = stack.pop()
        if not i or i in reachable: continue
        reachable.add(i)
        if rules[i][0] == 'c': stack.extend(rules[i][1:])
    exponents = [0]*len(rules)
    for i in sorted(reachable):
        r = rules[i]
        if r[0] == 't':
            if abs(r[1]) != g: return False
            exponents[i] = 1 if r[1] > 0 else -1
        else: exponents[i] = exponents[r[1]]+exponents[r[2]]
    return all(exponents[r] == 0 for r in roots)
