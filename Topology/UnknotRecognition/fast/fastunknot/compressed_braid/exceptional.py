"""Checked elementary reduction before an exceptional factor's complete cube."""
from ..braid_reduction import singleton_reduce, verify_singleton_reduction
from .cube import expand_leaf, produce as produce_cube
from .cube_verify import verify as verify_cube
from .engine import recognize as produce_three
from .grammar import Builder
from .verify import verify as verify_three, require


def word_grammar(strands, word, check):
    # Builder's balanced concatenations preserve short replay paths.
    b = Builder()
    def letters():
        for g in word:
            check()
            yield g
    if strands == 3:
        return b.data(b.word(letters()))
    rules, layer, terminals = [['e']], [], {}
    for g in letters():
        if g not in terminals:
            terminals[g] = len(rules)
            rules.append(['g', g])
        layer.append(terminals[g])
    while len(layer) > 1:
        following = []
        for i in range(0, len(layer), 2):
            check()
            if i+1 == len(layer):
                following.append(layer[i])
            else:
                following.append(len(rules))
                rules.append(['c', layer[i], layer[i+1]])
        layer = following
    return dict(strands=strands, rules=rules, root=layer[0] if layer else 0)


def reject_boolean_fields(certificate, check):
    # The two maintained Markov schemas have no Boolean fields. Reject Python's
    # bool/int aliases before handing a nested witness to the legacy verifier.
    pending = [certificate]
    while pending:
        check()
        value = pending.pop()
        require(type(value) is not bool, 'Boolean in integer reduction witness')
        if isinstance(value, dict):
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)


def produce(data, summary, *, max_crossings, reserve, **arena_options):
    check = arena_options.get('check', lambda: None)
    word = expand_leaf(data, summary['length'], max_crossings, check)
    strands, reduced, reduction = singleton_reduce(data['strands'], word, check)
    if strands == data['strands'] and list(reduced) == word:
        return produce_cube(data, summary, max_crossings=max_crossings,
                            check=check, reserve=reserve)
    source = word_grammar(strands, reduced, check)
    if strands == 3:
        result = produce_three(source, **arena_options)
        child, status = result['certificate'], result['status']
    else:
        # Avoid an import cycle: forest selects this adapter only at runtime.
        from .forest import summarize
        child = produce_cube(source, summarize(source, check=check),
                             max_crossings=max_crossings, check=check, reserve=reserve)
        status = child['status']
    if status not in ('UNKNOT', 'KNOTTED'):
        raise ArithmeticError('knot-preserving reduction produced a non-knot')
    return dict(version='exceptional-reduction-v1', status=status,
                reduction=reduction, terminal=child)


def verify(data, summary, certificate, *, max_crossings, reserve, **arena_options):
    check = arena_options.get('check', lambda: None)
    c = certificate
    require(isinstance(c, dict) and c.get('version') == 'exceptional-reduction-v1',
            'invalid exceptional reduction version')
    word = expand_leaf(data, summary['length'], max_crossings, check)
    reduction = c.get('reduction')
    reject_boolean_fields(reduction, check)
    strands, reduced = verify_singleton_reduction(data['strands'], word, reduction, check)
    source = word_grammar(strands, reduced, check)
    if strands == 3:
        status = verify_three(source, c.get('terminal'), **arena_options)
    else:
        from .forest import summarize
        status = verify_cube(source, summarize(source, check=check), c.get('terminal'),
                             max_crossings=max_crossings, check=check, reserve=reserve)
    require(status in ('UNKNOT', 'KNOTTED') and c.get('status') == status,
            'incorrect reduced-factor verdict')
    return status
