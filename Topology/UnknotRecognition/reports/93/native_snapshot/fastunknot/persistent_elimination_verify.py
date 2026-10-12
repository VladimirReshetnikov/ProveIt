"""Independent replay of consecutive raw singleton batches in one circuit.

Immutable signed concatenations share inverses. An eliminated generator gets
one binding, which updates all historical occurrences without rebuilding them.
Only the final roots are exported to the ordinary immutable WordArena. No
producer, equality, reduction, substitution or expanded-word helper is used.
"""
from collections import deque

from .compressed_words import CompressedLimit
from .elimination_batch_verify import _entries, _order


class _ReplayCircuit:
    def __init__(self, arena, roots):
        self.arena = arena
        self.rules = [None]
        self.depth = [0]
        self.interned = {}
        self.bindings = {}
        mapped = {0: 0}
        for node in arena._reachable(roots):
            arena.tick()
            rule = arena.rules[node]
            if rule[0] == 't':
                g = rule[1]
                value = self.intern(('t', abs(g)), 0)
                mapped[node] = value if g > 0 else -value
            else:
                mapped[node] = self.concat(mapped[rule[1]], mapped[rule[2]])
        self.roots = [mapped[root] for root in roots]
        self.initial_nodes = len(self.rules)-1
        self.initial_depth = max(self.depth)
        self.siblings = 0

    def capacity(self):
        total = len(self.arena.rules)+len(self.rules)-2
        stats = self.arena.stats
        stats['persistent_peak_nodes'] = max(stats.get('persistent_peak_nodes', 0), total)
        if total > self.arena.max_nodes:
            raise CompressedLimit('persistent replay combined node allowance exhausted')

    def intern(self, rule, depth):
        self.arena.tick()
        if rule in self.interned:
            return self.interned[rule]
        # Charge the ordinary historical arena and the private circuit together.
        if len(self.arena.rules)+len(self.rules)-2 >= self.arena.max_nodes:
            raise CompressedLimit('persistent replay combined node allowance exhausted')
        node = len(self.rules)
        self.rules.append(rule)
        self.depth.append(depth)
        self.interned[rule] = node
        self.capacity()
        return node

    def concat(self, left, right):
        self.arena.tick()
        if not left:return right
        if not right:return left
        return self.intern(('c', left, right),
                           1+max(self.depth[abs(left)], self.depth[abs(right)]))

    def balanced(self, pieces):
        nodes = [node for node in pieces if node]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i+1]) if i+1 < len(nodes)
                     else nodes[i] for i in range(0, len(nodes), 2)]
        return nodes[0] if nodes else 0

    def order(self):
        degree = [0]*len(self.rules)
        followers = [[] for _ in self.rules]
        for node, rule in enumerate(self.rules[1:], 1):
            self.arena.tick()
            if rule[0] == 'c':children = (abs(rule[1]), abs(rule[2]))
            else:
                target = self.bindings.get(rule[1], 0)
                children = (abs(target),) if target else ()
            degree[node] = len(children)
            for child in children:followers[child].append(node)
        queue = deque(node for node in range(1, len(self.rules)) if not degree[node])
        result = []
        while queue:
            self.arena.tick()
            node = queue.popleft()
            result.append(node)
            # Duplicate child edges are retained: c(x,x) has two dependencies.
            for user in followers[node]:
                degree[user] -= 1
                if not degree[user]:queue.append(user)
        return result if len(result) == len(self.rules)-1 else None

    def ranks(self, order, ranks, alive):
        high, count = [0]*len(self.rules), [0]*len(self.rules)
        for node in order:
            self.arena.tick()
            rule = self.rules[node]
            if rule[0] == 'c':
                left, right = abs(rule[1]), abs(rule[2])
                rank = max(high[left], high[right])
                high[node] = rank
                count[node] = min(2, (count[left] if high[left] == rank else 0)
                                 + (count[right] if high[right] == rank else 0))
            elif rule[1] in self.bindings:
                target = abs(self.bindings[rule[1]])
                high[node], count[node] = high[target], count[target]
            else:
                if rule[1] not in alive:return None
                high[node], count[node] = ranks.get(rule[1], 0), 1
        return high, count

    def legacy_order(self, order, entries):
        # Recover the selected dependency graph for unordered legacy evidence.
        # Only selected-generator bits are needed; ranks() checks all live labels.
        bits = {e['generator']: 1 << i for i, e in enumerate(entries)}
        support = [0]*len(self.rules)
        for node in order:
            self.arena.tick()
            rule = self.rules[node]
            if rule[0] == 'c':support[node] = support[abs(rule[1])] | support[abs(rule[2])]
            elif rule[1] in self.bindings:support[node] = support[abs(self.bindings[rule[1]])]
            else:support[node] = bits.get(rule[1], 0)
        dependencies = {}
        labels = [e['generator'] for e in entries]
        for entry in entries:
            g = entry['generator']
            mask = support[abs(self.roots[entry['relation']])] & ~bits[g]
            deps = set()
            while mask:
                self.arena.tick()
                bit = mask & -mask
                deps.add(labels[bit.bit_length()-1])
                mask ^= bit
            dependencies[g] = deps
        return _order(dependencies, self.arena.tick)

    def batch(self, alive, move):
        parsed = _entries(move, len(self.roots), alive, self.arena.tick)
        if parsed is None:return False
        children, slots = parsed
        entries = move['entries']
        order = self.order()
        if order is None:return False
        ranks = {e['generator']: i+1 for i, e in enumerate(entries)}
        summary = self.ranks(order, ranks, alive)
        if summary is None:return False

        def donors_valid():
            self.arena.tick(len(entries))
            high, count = summary
            return all(high[abs(self.roots[e['relation']])] == ranks[e['generator']]
                       and count[abs(self.roots[e['relation']])] == 1 for e in entries)

        if not donors_valid():
            selected = self.legacy_order(order, entries)
            if selected is None:return False
            ranks = {g: i+1 for i, g in enumerate(selected)}
            summary = self.ranks(order, ranks, alive)
            if summary is None or not donors_valid():return False
            stats = self.arena.stats
            stats['persistent_legacy_orders'] = stats.get('persistent_legacy_orders', 0)+1

        # Derive every context against the same pre-batch state. Bindings are
        # installed together only after all donor and acyclicity checks pass.
        high, _ = summary
        images = {}
        for entry in entries:
            g = entry['generator']
            current = self.roots[entry['relation']]
            before, after = [], []
            while True:
                self.arena.tick()
                orientation = 1 if current > 0 else -1
                rule = self.rules[abs(current)]
                if rule[0] == 't':
                    if rule[1] in self.bindings:
                        current = orientation*self.bindings[rule[1]]
                        continue
                    if rule[1] != g:return False
                    break
                left, right = rule[1:]
                if orientation < 0:left, right = -right, -left
                if high[abs(left)] == ranks[g]:
                    after.append(right)
                    current = left
                else:
                    before.append(left)
                    current = right
            self.siblings += len(before)+len(after)
            rest = self.balanced(list(reversed(after))+before)
            images[g] = -rest if orientation > 0 else rest
        self.bindings.update(images)
        for slot in slots:self.roots[slot] = 0
        alive.difference_update(children)
        return True

    def export(self):
        # Signed postorder follows bindings and only the retained roots.
        # Keep ordinary arena entries immutable; install no aliases in its caches.
        mapped, active = {0: 0}, set()
        for root in self.roots:
            pending = [(root, False)]
            while pending:
                self.arena.tick()
                handle, ready = pending.pop()
                if handle in mapped:continue
                rule = self.rules[abs(handle)]
                sign = 1 if handle > 0 else -1
                if rule[0] == 'c':
                    deps = rule[1:] if sign > 0 else (-rule[2], -rule[1])
                elif rule[1] in self.bindings:deps = (sign*self.bindings[rule[1]],)
                else:deps = ()
                if not ready:
                    if handle in active:return None
                    active.add(handle)
                    pending.append((handle, True))
                    pending.extend((child, False) for child in reversed(deps))
                    continue
                if not deps:value = self.arena.letter(sign*rule[1])
                elif len(deps) == 1:value = mapped[deps[0]]
                else:value = self.arena.concat(mapped[deps[0]], mapped[deps[1]])
                self.capacity()
                mapped[handle] = value
                active.remove(handle)
        return [mapped[root] for root in self.roots]


def replay_compressed_block(arena, roots, alive, moves):
    """Replay a supplied consecutive batch block; publish only on full success.

    The caller establishes that these are consecutive moves in the source-bound
    trace. All private circuit work uses the same cooperative arena allowance.
    The node cap charges private nodes and ordinary historical nodes together;
    finite-budget outcomes can differ from batch-at-a-time replay.
    """
    circuit = _ReplayCircuit(arena, roots)
    remaining = set(alive)
    for move in moves:
        arena.tick()
        if not circuit.batch(remaining, move):return False
    output = circuit.export()
    if output is None:return False
    stats = arena.stats
    stats['persistent_blocks'] = stats.get('persistent_blocks', 0)+1
    stats['persistent_batches'] = stats.get('persistent_batches', 0)+len(moves)
    stats['persistent_generators'] = stats.get('persistent_generators', 0)+len(circuit.bindings)
    stats['persistent_nodes'] = stats.get('persistent_nodes', 0)+len(circuit.rules)-1
    stats['persistent_context_siblings'] = stats.get('persistent_context_siblings', 0)+circuit.siblings
    stats['persistent_max_depth'] = max(stats.get('persistent_max_depth', 0), max(circuit.depth))
    roots[:] = output
    alive.clear()
    alive.update(remaining)
    return True
