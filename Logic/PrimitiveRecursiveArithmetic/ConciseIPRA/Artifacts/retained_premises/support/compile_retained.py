"""Compile successful canonical old-checker traces to retained-major proofs.

This is an untrusted certificate compiler. The standalone checker rechecks
all output. The compiler never changes the requested public goal.
"""
import copy
import json
from dataclasses import dataclass

BAD = object()


def opening(a, t=BAD, d=0, k=0):
    if a * 0 != 0:
        return [opening(b, t, d + 5 - len(a), k) for b in a]
    return a if k <= a < d else d % 2 and opening(t, d=3, k=k)


def rename(a, env):
    if isinstance(a, list):
        return [rename(b, env) for b in a]
    if type(a) is not int:
        raise ValueError('Compiler requires integer/list syntax')
    if a < 0:
        return env[a]
    return a


@dataclass
class Trace:
    goal: object
    k: int
    packet: object = None
    major: object = None
    continuation: object = None
    elimination: bool = False


def parse_old(certificate):
    packets = copy.deepcopy(certificate)
    public_goal = packets.pop()

    def check(a, g, k):
        if opening(a, k=k) in g:
            return Trace(a, k)
        m, s, u, t = packet = packets.pop()
        node = Trace(copy.deepcopy(a), k, packet)
        if (m, a) == (s and [s, u] or [t] * 3, opening(t, u, k=k)):
            b = opening(t, s, k=k)
            if b:
                a = b
                node.elimination = True
        node.major = check(m, g, k)
        if m:
            h = m * 3
        elif u:
            h = [[s and [s], u, t], opening(t, [s, u, t], 3, k) if s else u]
        else:
            a = opening(*a, t, 2, k)
            h = a
        k -= 1
        new_a = opening(a, [k], k=k)
        new_h = opening(h, (m or ~len(a) % 2) and k, k=k)
        node.continuation = check(new_a, g + [new_h], k)
        return node

    trace = check(public_goal, [0], 0)
    return public_goal, trace


class Finished(Exception):
    pass


def marker(n):
    if n == 0:
        return [0]
    return [0, marker(n // 2), [0] if n % 2 else 0]


def has_subtree(a, target):
    return a == target or isinstance(a, list) and any(has_subtree(b, target) for b in a)


def hole_template(a, target, d=0):
    if a == target:
        if not d % 2:
            raise ValueError('Marker at formula position')
        return d
    if isinstance(a, list):
        return [hole_template(b, target, d + 5 - len(a)) for b in a]
    return a


class Builder:
    def __init__(self, goal, g, k, stats):
        self.goal = goal
        self.g = list(g)
        self.k = k
        self.records = []
        self.serial = 0
        self.stats = stats

    def op(self, a, t=BAD, d=0, k=None):
        return opening(a, t, d, self.k if k is None else k)

    def fresh_marker(self, forbidden=()):
        while True:
            self.serial += 1
            term = marker(self.serial)
            if all(not has_subtree(a, term) for a in forbidden):
                return term

    def guard_padding(self):
        while True:
            s = self.fresh_marker()
            if [s, 0] not in self.g:
                return s

    def emit(self, packet, proof=()):
        if self.op(self.goal) in self.g:
            raise Finished
        m, s, u, t = packet
        expected = s and [s, u] or [t] * 3
        a = self.goal
        if expected in self.g:
            source = self.op(t, s)
            if not proof and source not in self.g:
                raise ValueError(('Missing forward minor', source))
            h = self.op(t, u)
            self.stats['forward_steps'] += 1
        else:
            if m:
                if not proof and self.op(m) not in self.g:
                    raise ValueError(('Missing major proof', m))
                h = m * 3
            elif u:
                h = self.computation(s, u, t)
                self.stats['computation_steps'] += 1
            else:
                a = self.op(*a, t, 2)
                h = a
                self.stats['introductions'] += 1
        self.records.append(packet)
        self.records.extend(proof)
        self.k -= 1
        self.goal = self.op(a, [self.k])
        self.g.append(self.op(h, (m or ~len(a) % 2) and self.k))
        if self.op(self.goal) in self.g:
            raise Finished

    def computation(self, s, u, t):
        return [[s and [s], u, t], self.op(t, [s, u, t], 3) if s else u]

    def allocate(self):
        # A harmless zero computation introduces one fresh numerical parameter.
        while True:
            t = self.fresh_marker()
            if [t] * 3 not in self.g:
                self.emit([0, 0, [0], t])
                self.stats['dummy_allocations'] += 1
                return self.k

    def compute(self, s, u, t):
        expected = s and [s, u] or [t] * 3
        if expected not in self.g:
            self.emit([0, s, u, t])
            return
        if not s:
            raise ValueError('A numerical update body collided with a retained Q')
        self.stats['computation_collisions'] += 1
        while True:
            witness = self.fresh_marker()
            seed = [0, u, witness]
            if [s, seed] not in self.g and not any(has_subtree(x, seed) for x in [s, t, *self.g]):
                break
        self.emit([0, 0, u, witness])  # seed = u
        expanded = self.computation(s, seed, t)
        desired = self.computation(s, u, t)
        frame = hole_template(expanded, seed)
        if self.op(frame, seed) != expanded or self.op(frame, u) != desired:
            raise ValueError('Seed frame does not instantiate correctly')
        self.emit([0, s, seed, t])
        self.emit([0, seed, u, frame])

    def derive(self, node, env):
        target = rename(node.goal, env)
        if self.op(self.goal) in self.g:
            raise Finished
        if node.packet is None:
            if self.op(target) not in self.g:
                raise ValueError(('Missing translated hypothesis', target, self.g))
            return
        m, s, u, t = (rename(x, env) for x in node.packet)
        if node.elimination:
            if len(m) not in (2, 3):
                raise ValueError('Elimination major is not Eq or Q')
            self.derive(node.major, env)
            if self.op(m) not in self.g:
                raise ValueError('Derived major was not retained')
            fresh = self.allocate()
            next_env = dict(env, **{})
            next_env[node.k - 1] = fresh
            minor_goal = rename(node.continuation.goal, next_env)
            if minor_goal != self.op(t, s):
                raise ValueError(('Minor goal mismatch', minor_goal, self.op(t, s)))
            proof = build(node.continuation, self.g, self.k, next_env, self.stats)
            self.emit([0, s, u, t], proof)
            if self.op(target) not in self.g:
                raise ValueError(('Forward target mismatch', target))
            return
        if m:
            if isinstance(m, list) and len(m) == 1:
                proof = build(node.major, self.g, self.k, env, self.stats)
                self.emit([m, self.guard_padding(), 0, 0], proof)
                self.stats['D_eliminations'] += 1
            else:
                # Non-eliminating Eq/Q majors contribute only administrative padding.
                self.allocate()
        elif u:
            self.compute(s, u, t)
        else:
            if self.goal != target:
                raise ValueError('A D introduction cannot be inlined into an unrelated goal')
            self.emit([0, self.guard_padding(), 0, t])
        next_env = dict(env)
        next_env[node.k - 1] = self.k
        self.derive(node.continuation, next_env)


def build(node, g, k, env, stats):
    b = Builder(rename(node.goal, env), g, k, stats)
    try:
        b.derive(node, env)
        if b.op(b.goal) not in b.g:
            raise ValueError('Compilation ended without a retained goal')
    except Finished:
        pass
    return b.records


def compile_certificate(certificate):
    goal, trace = parse_old(certificate)
    stats = dict.fromkeys(('forward_steps', 'computation_steps', 'introductions', 'dummy_allocations', 'computation_collisions', 'D_eliminations'), 0)
    execution = build(trace, [0], 0, {}, stats)
    return list(reversed(execution)) + [goal], stats


if __name__ == '__main__':
    import sys
    source = json.load(open(sys.argv[1]))
    output, stats = compile_certificate(source)
    json.dump(output, open(sys.argv[2], 'w'), separators=(',', ':'))
    print(json.dumps(stats))
