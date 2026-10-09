"""Read-only adapter for the inspected fastunknot.WordArena t/c rule schema.

A proposal, not a production recognizer patch. All returned objects are
algebraic evidence; an existing PD/trace replayer must consume them. The adapter
charges arena.tick() for every retained source node and every query pass.
"""
from christoffel import scan_aligned, Limits


def query_wordarena(arena, roots, alive, *, max_bits=100_000):
    labels = sorted(alive)
    if len(labels) != 2:
        return {'status': 'UNSUPPORTED_RANK'}
    rename = {labels[0]: 1, -labels[0]: -1, labels[1]: 2, -labels[1]: -2}
    # Traverse only ancestors of queried roots; preserve relator slot order.
    seen, todo = set(), list(roots)
    while todo:
        arena.tick()
        node = todo.pop()
        if node == 0 or node in seen:
            continue
        seen.add(node)
        rule = arena.rules[node]
        if rule[0] == 'c':
            todo.extend(rule[1:])
    mapping, rules = {0: 0}, [None]
    for node in sorted(seen):
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            translated = ('t', rename[rule[1]])
        else:
            translated = ('c', mapping[rule[1]], mapping[rule[2]])
        mapping[node] = len(rules)
        rules.append(translated)
    result = scan_aligned(rules, [mapping[r] for r in roots],
                          limits=Limits(max_nodes=len(rules), max_bits=max_bits),
                          check=arena.tick)
    result.update(labels=labels, rules=rules, roots=[mapping[r] for r in roots])
    return result
