"""Independent raw replay of simultaneous singleton Tietze eliminations.

The source wrapper reconstructs every Wirtinger relator. This module accepts
only original slot/child claims, checks their literal singleton occurrences,
and rejects cycles in the full signed substitution grammar. It never imports
the producer, and it never trusts supplied replacement words or dependencies.
"""


def _pivots(move, alive, slots, tick):
    tick()
    if (type(move) is not dict or set(move) != {'kind', 'pivots'}
            or move['kind'] != 'singleton_dag'):
        return None
    records = move['pivots']
    if type(records) is not list or not records or len(records) > len(alive):
        return None
    children, donors, result = set(), set(), []
    for record in records:
        tick()
        if type(record) is not dict or set(record) != {'relation', 'generator'}:
            return None
        slot, child = record['relation'], record['generator']
        if (type(slot) is not int or not 0 <= slot < slots or slot in donors
                or type(child) is not int or child not in alive or child in children):
            return None
        donors.add(slot)
        children.add(child)
        result.append((slot, child))
    return result, children, donors


def replay_compressed_singleton_dag(arena, roots, alive, move):
    """Check and apply a raw DAG quotient, leaving inputs intact on rejection.

    The pivot list supplies a topological order. Give survivors rank zero and
    pivots increasing ranks; each donor must contain its own pivot exactly once
    as its unique largest-rank letter. Constant-size summaries check this for
    any correctly ordered DAG, independently of the numeric generator labels.
    The signed grammar walk also checks all unreferenced donor definitions.
    """
    data = _pivots(move, alive, len(roots), arena.tick)
    if data is None:
        return False
    records, children, donors = data
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

    definitions = {}
    for slot, child in records:
        arena.tick()
        root = roots[slot]
        rank = ranks[child]
        if maximum[root] != rank or count[root] != 1:
            return False
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
    arena.stats['singleton_dag_replays'] = arena.stats.get('singleton_dag_replays', 0) + 1
    return True


def replay_literal_singleton_dag(words, alive, move, budget):
    """Independent explicit Tietze replay with allocation checks before growth."""
    data = _pivots(move, alive, len(words), budget.tick)
    if data is None:
        return False
    records, children, donors = data
    bodies = {}
    for word in words:
        budget.tick(len(word) + 1)
        if any(abs(value) not in alive for value in word):
            return False
    for slot, child in records:
        word = words[slot]
        budget.tick(len(word) + 1)
        positions = [i for i, value in enumerate(word) if abs(value) == child]
        if len(positions) != 1 or any(abs(value) not in alive for value in word):
            return False
        position = positions[0]
        rest = word[position + 1:] + word[:position]
        bodies[child] = ([-value for value in reversed(rest)]
                         if word[position] > 0 else rest)
    ranks = {child: index + 1 for index, (_, child) in enumerate(records)}
    for child, word in bodies.items():
        budget.tick(len(word) + 1)
        if any(ranks.get(abs(value), 0) >= ranks[child] for value in word):
            return False
    parents = {child: {abs(value) for value in word} & children
               for child, word in bodies.items()}
    consumers = {child: [] for child in children}
    remaining = {child: len(deps) for child, deps in parents.items()}
    for child, deps in parents.items():
        budget.tick(len(deps) + 1)
        for parent in deps:
            consumers[parent].append(child)
    queue = [child for child in bodies if not remaining[child]]
    for parent in queue:
        budget.tick()
        for child in consumers[parent]:
            remaining[child] -= 1
            if not remaining[child]:
                queue.append(child)
    if len(queue) != len(children):
        return False

    images, allocated = {}, 0

    def expand_checked(word):
        nonlocal allocated
        budget.tick(len(word) + 1)
        length = sum(len(images.get(value, (value,))) for value in word)
        budget.size(allocated + length)
        budget.tick(length)
        allocated += length
        return [letter for value in word for letter in images.get(value, (value,))]

    for child in queue:
        image = expand_checked(bodies[child])
        budget.size(allocated + len(image))
        budget.tick(len(image))
        allocated += len(image)
        images[child] = image
        images[-child] = [-value for value in reversed(image)]
    result = [([] if slot in donors else expand_checked(word))
              for slot, word in enumerate(words)]
    words[:] = result
    alive.difference_update(children)
    return True
