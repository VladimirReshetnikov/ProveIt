"""Independent rank-summary and virtual-sign replay of ordered batch witnesses.

Adapted from report 51. The caller has checked the existing v8 entry schema;
this module reconstructs the claimed order and every image from raw source
words. It imports no producer or normalization code. Unordered legacy evidence
is returned to the existing complete checker without publishing partial state.
"""


def replay_ordered_batch(arena, roots, alive, entries, children, donors):
    """Check and apply a raw DAG quotient, leaving inputs intact on rejection.

    Return None when the entry order needs the legacy graph checker.
    The pivot list supplies a topological order. Give survivors rank zero and
    pivots increasing ranks; each donor must contain its own pivot exactly once
    as its unique largest-rank letter. Constant-size summaries check this for
    any correctly ordered DAG, independently of the numeric generator labels.
    The signed grammar walk also checks all unreferenced donor definitions.
    """
    records = [(entry['relation'], entry['generator']) for entry in entries]
    ranks = {child: index + 1 for index, (_, child) in enumerate(records)}
    reachable = arena._reachable(roots)
    maximum, count = {0: 0}, {0: 0}
    for node in reachable:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            label = abs(rule[1])
            if label not in alive:
                return False
            maximum[node], count[node] = ranks.get(label, 0), 1
        else:
            left, right = rule[1:]
            high = max(maximum[left], maximum[right])
            maximum[node] = high
            count[node] = min(2, (count[left] if maximum[left] == high else 0)
                             + (count[right] if maximum[right] == high else 0))

    arena.stats['elimination_ordered_nodes'] = arena.stats.get('elimination_ordered_nodes', 0) + len(reachable)
    # An unordered legacy witness may be valid. Fall back before allocating
    # contexts, while no published roots or live labels have changed.
    for slot, child in records:
        arena.tick()
        root = roots[slot]
        if maximum[root] != ranks[child] or count[root] != 1:
            return None

    definitions = {}
    for slot, child in records:
        arena.tick()
        root = roots[slot]
        rank = ranks[child]
        contains = lambda node: maximum[node] == rank
        node, position = root, 0
        while arena.rules[node][0] == 'c':
            arena.tick()
            left, right = arena.rules[node][1:]
            if contains(left):
                node = left
            else:
                position += arena.lengths[left]
                node = right
        epsilon = 1 if arena.rules[node][1] > 0 else -1
        suffix = arena.slice(root, position + 1, arena.lengths[root])
        prefix = arena.slice(root, 0, position)
        definitions[child] = (arena.concat(suffix, prefix), -epsilon)

    values = {(0, 1): 0, (0, -1): 0}
    active = set()

    def dependencies(key):
        node, sign = key
        rule = arena.rules[node]
        if rule[0] == 't':
            child = abs(rule[1])
            if child not in definitions:
                return ()
            body, polarity = definitions[child]
            return ((body, polarity * sign * (1 if rule[1] > 0 else -1)),)
        left, right = rule[1:]
        return ((left, 1), (right, 1)) if sign == 1 else ((right, -1), (left, -1))

    # Include each definition, even if no surviving root mentions its child.
    goals = list(definitions.values())
    goals.extend((root, 1) for slot, root in enumerate(roots) if slot not in donors)
    for goal in goals:
        pending = [(goal, False)]
        while pending:
            arena.tick()
            key, ready = pending.pop()
            if key in values:
                continue
            if not ready:
                if key in active:
                    return False
                active.add(key)
                pending.append((key, True))
                pending.extend((child, False) for child in reversed(dependencies(key)))
                continue
            needed = dependencies(key)
            if not needed:
                node, sign = key
                values[key] = arena.letter(arena.rules[node][1] * sign)
            elif len(needed) == 1:
                values[key] = values[needed[0]]
            else:
                values[key] = arena.concat(values[needed[0]], values[needed[1]])
            active.remove(key)
    result = [0 if slot in donors else values[(root, 1)]
              for slot, root in enumerate(roots)]
    roots[:] = result
    alive.difference_update(children)
    arena.stats['elimination_ordered_replays'] = arena.stats.get('elimination_ordered_replays', 0) + 1
    return True
