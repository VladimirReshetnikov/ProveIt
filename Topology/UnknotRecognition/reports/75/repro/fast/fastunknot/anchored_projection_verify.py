"""Independent replay of raw monomial blocks on an immutable source grammar.

Consecutive primitive projections and unit-coordinate forests update only a
signed monomial image table. Donors are authenticated on the original word
circuit under that table; ordinary words are exported once after the block.
The caller must have independently recovered the source knot presentation.
"""
from .primitive_power_verify import _header
from .primitive_projection_verify import _selection
from .primitive_forest_verify import _images


class _SourceReplay:
    def __init__(self, arena, roots, alive):
        arena.tick(len(roots)+len(alive)+1)
        self.arena = arena
        self.roots = tuple(roots)
        self.images = {g: (g, 1) for g in alive}
        self.alive = set(alive)
        self.dead = set()
        self.lengths = {0: 0}
        self.length_nodes = 0
        self.max_bits = 1

    def length(self, slot):
        if slot in self.dead:
            return 0
        root = self.roots[slot]
        pending = [(root, False)]
        while pending:
            self.arena.tick()
            node, ready = pending.pop()
            if node in self.lengths:
                continue
            rule = self.arena.rules[node]
            if rule[0] == 'c' and not ready:
                pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:
                self.lengths[node] = (abs(self.images[abs(rule[1])][1]) if rule[0] == 't'
                                      else self.lengths[rule[1]]+self.lengths[rule[2]])
                self.length_nodes += 1
        return self.lengths[root]

    def verify(self, proof, pair):
        arena = self.arena
        header = _header(proof, pair, len(self.roots), self.length, arena.tick)
        if header is None:
            return False
        slot, labels, u, v, exponent, width = header
        signed = (labels[0], -labels[0], labels[1], -labels[1])
        increments = (v, -v, -u, u)
        memo = {0: ((0,0,0,0), 0, 0, 0)}
        root = self.roots[slot]
        pending = [(root, False)]
        while pending:
            arena.tick()
            node, ready = pending.pop()
            if node in memo:
                continue
            rule = arena.rules[node]
            if rule[0] == 't':
                label, power = self.images[abs(rule[1])]
                if rule[1] < 0:
                    power = -power
                letter = label if power > 0 else -label
                if letter not in signed:
                    return False
                index = signed.index(letter)
                counts = [0]*4
                counts[index] = abs(power)
                height = increments[index]*abs(power)
                memo[node] = tuple(counts), height, min(0,height), max(0,height)
            elif not ready:
                pending.extend(((node, True), (rule[2], False), (rule[1], False)))
            else:
                left, h, low, high = memo[rule[1]]
                right, k, bottom, top = memo[rule[2]]
                memo[node] = (tuple(a+b for a,b in zip(left,right)), h+k,
                              min(low,h+bottom), max(high,h+top))
        (a,A,b,B), _, low, high = memo[root]
        arena.tick()
        return (not (a and A or b and B) and a-A == exponent*u
                and b-B == exponent*v and high-low == width)

    def apply(self, move):
        self.lengths = {0: 0}
        if type(move) is not dict:
            return False
        if move.get('kind') == 'primitive_projection':
            selected = _selection(move, self.alive, self.verify, self.arena.tick)
            if selected is None:
                return False
            local, slots, removed = {}, set(), set()
            for proof in selected:
                self.arena.tick()
                a,b = proof['generators']
                u,v = proof['primitive_vector']
                local[a], local[b] = (a,abs(v)), (a,-u if v>0 else u)
                slots.add(proof['relation'])
                removed.add(b)
        elif move.get('kind') == 'primitive_forest':
            data = _images(move, self.alive, self.verify, self.arena.tick)
            if data is None:
                return False
            local, slots, _ = data
            removed = set(local)
        else:
            return False
        updated = {}
        for original, (label, power) in self.images.items():
            self.arena.tick()
            target, factor = local.get(label, (label,1))
            exponent = power*factor
            updated[original] = target, exponent
            self.max_bits = max(self.max_bits, abs(exponent).bit_length())
        self.images = updated
        self.dead.update(slots)
        self.alive.difference_update(removed)
        return True

    def export(self):
        arena = self.arena
        mapped, powers = {0: 0}, {}
        output = []
        for slot, root in enumerate(self.roots):
            arena.tick()
            if slot in self.dead:
                output.append(0)
                continue
            pending = [(root,False)]
            while pending:
                arena.tick()
                node, ready = pending.pop()
                if node in mapped:
                    continue
                rule = arena.rules[node]
                if rule[0] == 't':
                    label, power = self.images[abs(rule[1])]
                    power *= 1 if rule[1]>0 else -1
                    key = label,power
                    if key not in powers:
                        powers[key] = arena.power(arena.letter(label if power>0 else -label),abs(power))
                    mapped[node] = powers[key]
                elif not ready:
                    pending.extend(((node,True),(rule[2],False),(rule[1],False)))
                else:
                    mapped[node] = arena.concat(mapped[rule[1]],mapped[rule[2]])
            output.append(mapped[root])
        return output


def replay_compressed_monomial_block(arena, roots, alive, moves):
    """Check a supplied block; publish roots/live labels only after final export."""
    state = _SourceReplay(arena, roots, alive)
    for move in moves:
        arena.tick()
        if not state.apply(move):
            return False
    output = state.export()
    arena.tick()
    roots[:] = output
    alive.clear()
    alive.update(state.alive)
    stats = arena.stats
    stats['anchored_replay_blocks'] = stats.get('anchored_replay_blocks',0)+1
    stats['anchored_replay_rounds'] = stats.get('anchored_replay_rounds',0)+len(moves)
    stats['anchored_replay_length_nodes'] = stats.get('anchored_replay_length_nodes',0)+state.length_nodes
    stats['anchored_replay_max_exponent_bits'] = max(stats.get('anchored_replay_max_exponent_bits',0),state.max_bits)
    return True
