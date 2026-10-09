"""Singular-safe field-plan traversal for the dynamic-terminal research kernel.

The caller supplies the prepared, prime-specific kernel protocol from the
dynamic-terminal report: b, nullity, cursor(budget), and persistent cursors
with residue and merged(target, source, budget). This module has no runtime
recognizer dispatch and does not itself certify the graph's knot geometry.
"""


def field_plan(kernel, events, observations, *, check=None, stats=None):
    """Evaluate a supplied merge tree, pruning q < interior-nullity cones.

    All merge labels are checked even inside pruned cones. Preparation and
    integer reconstruction belong to the caller. Callbacks propagate; a
    failed call returns no partial answers and does not mutate the kernel.
    """
    def tick(units=1):
        if check is not None:
            check()
        if stats is not None:
            stats['work'] = stats.get('work', 0) + units

    def count(name):
        if stats is not None:
            stats[name] = stats.get(name, 0)+1

    class Budget:
        def tick(self, units=1):
            tick(units)

    budget = Budget() if check is not None or stats is not None else None
    b = kernel.b
    if type(b) is not int or b < 1:
        raise ValueError('positive terminal count required')
    tree = [[] for _ in range(len(events)+1)]
    for node, event in enumerate(events, 1):
        tick()
        if len(event) != 3 or any(type(x) is not int for x in event):
            raise ValueError('merge events require three integers')
        parent, target, source = event
        if not 0 <= parent < node:
            raise ValueError('parents must precede children')
        tree[parent].append((node, target, source))
    for node in observations:
        tick()
        if type(node) is not int or not 0 <= node < len(tree):
            raise ValueError('invalid observation node')

    # Validate the whole tree independently of any algebraic pruning. Keep
    # just one active anchor set, undoing each deletion on DFS return.
    anchors = set(range(b))
    stack = [(iter(tree[0]), None)]
    while stack:
        tick()
        children, restore = stack[-1]
        edge = next(children, None)
        if edge is None:
            stack.pop()
            if restore is not None:
                anchors.add(restore)
            continue
        node, target, source = edge
        if source == 0 or source == target or source not in anchors or target not in anchors:
            raise ValueError('merge requires two live anchors and a non-root source')
        anchors.remove(source)
        stack.append((iter(tree[node]), source))

    values = [0]*len(tree)
    r = kernel.nullity
    if r > b-1:
        count('zero_cones')
        tick()
        return [0 for _ in observations]
    root = kernel.cursor(budget)
    values[0] = root.residue
    stack = [(root, b-1, iter(tree[0]))]
    while stack:
        tick()
        state, q, children = stack[-1]
        edge = next(children, None)
        if edge is None:
            stack.pop()
            continue
        node, target, source = edge
        if q-1 < r:
            # Every descendant has still fewer blocks; values were zeroed.
            # No clone, rank update or descendant traversal is needed here.
            count('zero_cones')
            continue
        child = state.merged(target, source, budget)
        count('updated_edges')
        values[node] = child.residue
        stack.append((child, q-1, iter(tree[node])))
    tick()
    return [values[node] for node in observations]
