"""Raw simultaneous Tietze elimination along an acyclic dependency graph.

The producer selects a donor only when its largest generator occurs once.
Every other generator in its defining word is then smaller, so arbitrary
overlap among donors is safe.  Application also supports internally checked
acyclic schedules which do not respect that particular generator order.

These are algebraic operations, not verdict APIs.  A source-bound certificate
checker must reconstruct the presentation and independently replay the batch.
"""


def plan_singleton_dag(arena, roots, alive, cache=None):
    """Select the first defining relator for each eligible maximum generator.

    An immutable node summary contains its largest absolute generator label
    and that generator's occurrence count, capped at two.  No word lengths,
    expanded counts, support sets, or normalization are needed for selection.
    The cache stores only word content; slots and live membership are fresh.
    Pivots are returned in increasing generator order, explicitly witnessing
    the dependency order required by the certificate format.
    """
    if cache is None:
        cache = {}
    summaries = cache.setdefault('singleton_maxima', {0: (0, 0)})
    arena.stats['singleton_dag_attempts'] = arena.stats.get('singleton_dag_attempts', 0) + 1
    selected, used = [], set()
    for slot, root in enumerate(roots):
        arena.tick()
        pending = [(root, False)]
        while pending:
            arena.tick()
            node, ready = pending.pop()
            if node in summaries:
                continue
            rule = arena.rules[node]
            if rule[0] == 't':
                summary = abs(rule[1]), 1
            elif not ready:
                pending.extend(((node, True), (rule[2], False), (rule[1], False)))
                continue
            else:
                left, right = summaries[rule[1]], summaries[rule[2]]
                if left[0] > right[0]:
                    summary = left
                elif left[0] < right[0]:
                    summary = right
                else:
                    summary = left[0], min(2, left[1] + right[1])
            summaries[node] = summary
            arena.stats['singleton_dag_metadata_nodes'] = (
                arena.stats.get('singleton_dag_metadata_nodes', 0) + 1)
        child, count = summaries[root]
        if count == 1 and child in alive:
            arena.stats['singleton_dag_candidate_slots'] = (
                arena.stats.get('singleton_dag_candidate_slots', 0) + 1)
            if child not in used:
                selected.append(dict(relation=slot, generator=child))
                used.add(child)
    arena.tick(len(selected) * (len(selected).bit_length() + 1))
    selected.sort(key=lambda pivot: pivot['generator'])
    return selected


def apply_singleton_dag(arena, roots, alive, selected):
    """Apply an internally proved singleton schedule without free reduction.

    Each donor has one occurrence of its chosen child, children and slots are
    distinct, and a donor's other eliminated generators precede it in some
    acyclic order.  This routine checks uniqueness and detects dependency
    cycles, but is deliberately not the independent certificate verifier.

    All donor checks and raw composition finish before roots or ``alive``
    change.  Resource exhaustion may allocate arena nodes but does not commit
    a partial presentation.  A nonempty batch may eliminate every generator
    of an abstract trivial presentation; knot endpoints are checked outside.
    """
    if not selected:
        return
    original_nodes = len(arena.rules)
    chosen, slots = {}, set()
    for pivot in selected:
        arena.tick()
        slot, child = pivot['relation'], pivot['generator']
        if (type(slot) is not int or not 0 <= slot < len(roots)
                or type(child) is not int or child not in alive
                or child in chosen or slot in slots):
            raise ValueError('singleton schedule has an invalid child or donor slot')
        chosen[child] = slot
        slots.add(slot)

    # A topologically ordered schedule needs just two small integers per
    # reachable node: greatest pivot rank and its capped occurrence count.
    # The producer supplies such an order.  General internal schedules given
    # in another order use a mask fallback, with bits independent of labels.
    reachable = arena._reachable([roots[slot] for slot in slots])
    ranks = {child: index + 1 for index, child in enumerate(chosen)}
    maxima = {0: (0, 0)}
    for node in reachable:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            maxima[node] = ranks.get(abs(rule[1]), 0), 1
        else:
            left, right = rule[1:]
            a, b = maxima[left], maxima[right]
            maxima[node] = a if a[0] > b[0] else b if a[0] < b[0] else (a[0], min(2, a[1] + b[1]))
        arena.stats['singleton_dag_support_nodes'] = (
            arena.stats.get('singleton_dag_support_nodes', 0) + 1)
    arena.tick(len(chosen))
    ordinary = all(maxima[roots[slot]][0] == ranks[child] for child, slot in chosen.items())
    if ordinary:
        def contains(node, child):
            return maxima[node][0] == ranks[child]
    else:
        bits = {child: 1 << index for index, child in enumerate(chosen)}
        present, repeated = {0: 0}, {0: 0}
        for node in reachable:
            arena.tick()
            rule = arena.rules[node]
            if rule[0] == 't':
                present[node], repeated[node] = bits.get(abs(rule[1]), 0), 0
            else:
                left, right = rule[1:]
                present[node] = present[left] | present[right]
                repeated[node] = (repeated[left] | repeated[right]
                                  | (present[left] & present[right]))
            arena.stats['singleton_dag_general_mask_nodes'] = (
                arena.stats.get('singleton_dag_general_mask_nodes', 0) + 1)

        def contains(node, child):
            return bool(present[node] & bits[child])
    for child, slot in chosen.items():
        arena.tick()
        root = roots[slot]
        singleton = (maxima[root][1] == 1 if ordinary else
                     bool(present[root] & bits[child]) and not repeated[root] & bits[child])
        if not singleton:
            raise ValueError('singleton donor does not contain its child exactly once')

    # If R = prefix * child^epsilon * suffix, then
    # child = (suffix * prefix)^(-epsilon).  Inverse orientation remains a
    # virtual sign; neither construction nor composition calls arena.inverse.
    templates = {}
    for child, slot in chosen.items():
        arena.tick()
        node, prefix, suffix = roots[slot], 0, 0
        while arena.rules[node][0] == 'c':
            arena.tick()
            arena.stats['singleton_dag_path_steps'] = (
                arena.stats.get('singleton_dag_path_steps', 0) + 1)
            _, left, right = arena.rules[node]
            if contains(left, child):
                suffix = arena.concat(right, suffix)
                node = left
            else:
                prefix = arena.concat(prefix, left)
                node = right
        sign = 1 if arena.rules[node][1] > 0 else -1
        templates[child] = arena.concat(suffix, prefix), -sign

    # An augmented signed grammar combines ordinary concatenation edges with
    # a terminal-to-template edge for each eliminated generator.  Its graph is
    # acyclic exactly when the selected generator dependencies are acyclic.
    # Memoizing this graph composes all substitutions together; composing each
    # child separately would revisit long shared defining words many times.
    mapped = {(0, 1): 0, (0, -1): 0}
    active = set()

    def dependencies(node, sign):
        rule = arena.rules[node]
        if rule[0] == 'c':
            left, right = rule[1:]
            return ((left, 1), (right, 1)) if sign > 0 else ((right, -1), (left, -1))
        letter = rule[1]
        template = templates.get(abs(letter))
        if template is None:
            return ()
        replacement, orientation = template
        return ((replacement, orientation * sign * (1 if letter > 0 else -1)),)

    def evaluate(root, orientation=1):
        pending = [((root, orientation), False)]
        while pending:
            arena.tick()
            key, ready = pending.pop()
            if key in mapped:
                continue
            node, sign = key
            rule = arena.rules[node]
            children = dependencies(node, sign)
            if ready:
                mapped[key] = (arena.concat(mapped[children[0]], mapped[children[1]])
                               if rule[0] == 'c' else mapped[children[0]])
                active.remove(key)
            elif not children:
                mapped[key] = node if sign > 0 else arena.letter(-rule[1])
            else:
                if key in active:
                    raise ValueError('singleton generator dependencies contain a cycle')
                active.add(key)
                pending.append((key, True))
                pending.extend((child, False) for child in reversed(children))
                continue
            arena.stats['singleton_dag_evaluation_states'] = (
                arena.stats.get('singleton_dag_evaluation_states', 0) + 1)
        return mapped[root, orientation]

    # Evaluate both images even if every occurrence is in a discarded donor.
    # This validates the complete schedule and prevents an unused dependency
    # cycle from slipping past the internal acyclicity guard.
    for replacement, orientation in templates.values():
        arena.tick()
        evaluate(replacement, orientation)
        evaluate(replacement, -orientation)
    result = []
    for slot, root in enumerate(roots):
        arena.tick()
        result.append(0 if slot in slots else evaluate(root))
    roots[:] = result
    alive.difference_update(chosen)
    arena.stats['singleton_dag_rounds'] = arena.stats.get('singleton_dag_rounds', 0) + 1
    arena.stats['singleton_dag_pivots'] = arena.stats.get('singleton_dag_pivots', 0) + len(chosen)
    arena.stats['singleton_dag_max_batch'] = max(
        arena.stats.get('singleton_dag_max_batch', 0), len(chosen))
    arena.stats['singleton_dag_new_nodes'] = (
        arena.stats.get('singleton_dag_new_nodes', 0) + len(arena.rules) - original_nodes)
