"""Binary straight-line programs for braid words; no expanded allocation."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Summary:
    lengths: tuple
    exponents: tuple
    permutations: tuple
    root: int

    @property
    def knot(self):
        p = self.permutations[self.root]
        return p[0] != 0 and p[p[0]] != 0 and p[p[p[0]]] == 0


def validate(data, *, check=lambda: None):
    check()
    if not isinstance(data, dict) or set(data) != {'strands', 'rules', 'root'}:
        raise ValueError('expected strands/rules/root only')
    if type(data['strands']) is not int or data['strands'] != 3:
        raise ValueError('this backend accepts exactly three strands')
    rules, root = data['rules'], data['root']
    if not isinstance(rules, list) or not rules or rules[0] != ['e']:
        raise ValueError('rule zero must be ["e"]')
    if type(root) is not int or not 0 <= root < len(rules):
        raise ValueError('invalid root')
    lengths, exponents, permutations = [0], [0], [(0, 1, 2)]
    for i, rule in enumerate(rules[1:], 1):
        check()
        if not isinstance(rule, list) or not rule:
            raise ValueError('invalid rule')
        if rule[0] == 'g' and len(rule) == 2:
            g = rule[1]
            if type(g) is not int or g not in (-2, -1, 1, 2):
                raise ValueError('invalid Artin generator')
            p = [0, 1, 2]
            a = abs(g) - 1
            p[a], p[a + 1] = p[a + 1], p[a]
            lengths.append(1)
            exponents.append(1 if g > 0 else -1)
            permutations.append(tuple(p))
        elif rule[0] == 'c' and len(rule) == 3:
            a, b = rule[1:]
            if any(type(v) is not int or not 0 <= v < i for v in (a, b)):
                raise ValueError('rules must reference strictly earlier nodes')
            lengths.append(lengths[a] + lengths[b])
            exponents.append(exponents[a] + exponents[b])
            p, q = permutations[a], permutations[b]
            permutations.append(tuple(p[q[j]] for j in range(3)))
        else:
            raise ValueError('only g/c rules after the empty node are allowed')
    return Summary(tuple(lengths), tuple(exponents), tuple(permutations), root)


class Builder:
    def __init__(self):
        self.rules, self.index, self.inv = [['e']], {}, {0: 0}

    def _add(self, rule):
        key = tuple(rule)
        if key not in self.index:
            self.index[key] = len(self.rules)
            self.rules.append(rule)
        return self.index[key]

    def letter(self, g):
        if type(g) is not int or g not in (-2, -1, 1, 2):
            raise ValueError('invalid Artin generator')
        return self._add(['g', g])

    def concat(self, a, b):
        if not a:
            return b
        if not b:
            return a
        return self._add(['c', a, b])

    def word(self, word):
        nodes = [self.letter(g) for g in word]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i+1]) if i+1 < len(nodes) else nodes[i]
                     for i in range(0, len(nodes), 2)]
        return nodes[0] if nodes else 0

    def inverse(self, root):
        pending = [(root, False)]
        while pending:
            node, ready = pending.pop()
            if node in self.inv:
                continue
            rule = self.rules[node]
            if rule[0] == 'g':
                result = self.letter(-rule[1])
            elif ready:
                result = self.concat(self.inv[rule[2]], self.inv[rule[1]])
            else:
                pending.extend(((node, True), (rule[1], False), (rule[2], False)))
                continue
            self.inv[node], self.inv[result] = result, node
        return self.inv[root]

    def power(self, root, exponent):
        if type(exponent) is not int:
            raise ValueError('integer power required')
        if exponent < 0:
            root, exponent = self.inverse(root), -exponent
        answer = 0
        while exponent:
            if exponent & 1:
                answer = self.concat(answer, root)
            exponent >>= 1
            if exponent:
                root = self.concat(root, root)
        return answer

    def data(self, root):
        data = dict(strands=3, rules=[r[:] for r in self.rules], root=root)
        validate(data)
        return data


def expand(data, limit=100000):
    summary = validate(data)
    if summary.lengths[summary.root] > limit:
        raise ValueError('explicit oracle cap exceeded')
    result, pending = [], [summary.root]
    while pending:
        rule = data['rules'][pending.pop()]
        if rule[0] == 'g':
            result.append(rule[1])
        elif rule[0] == 'c':
            pending.extend((rule[2], rule[1]))
    return result
