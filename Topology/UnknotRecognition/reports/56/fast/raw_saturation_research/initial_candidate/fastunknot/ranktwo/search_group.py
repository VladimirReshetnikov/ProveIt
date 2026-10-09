"""Persistent exact B3 prefix states; deliberately no cyclic reduction.

The quotient is <x,y | x^2=y^3=1>. Tokens 0,1,2 mean x,y,y^2.
A node is an exact canonical reduced word, not a probabilistic fingerprint.
The extra exponent sum distinguishes all central lifts.
"""
from __future__ import annotations

_IMAGES = {1: (2, 0), -1: (0, 1), 2: (0, 2), -2: (1, 0)}


class QuotientTrie:
    __slots__ = ('parent', 'token', 'children', 'token_steps')

    def __init__(self) -> None:
        self.parent = [-1]
        self.token = [-1]
        self.children = [[-1, -1, -1]]
        self.token_steps = 0

    def _push(self, parent: int, token: int) -> int:
        child = self.children[parent][token]
        if child == -1:
            child = len(self.parent)
            self.children[parent][token] = child
            self.parent.append(parent)
            self.token.append(token)
            self.children.append([-1, -1, -1])
        return child

    def append_token(self, node: int, token: int) -> int:
        self.token_steps += 1
        if node and ((self.token[node] == 0) == (token == 0)):
            previous = self.token[node]
            node = self.parent[node]
            if token == 0:
                return node
            product = (previous + token) % 3
            return self._push(node, product) if product else node
        return self._push(node, token)

    def append_generator(self, node: int, generator: int) -> int:
        for token in _IMAGES[generator]:
            node = self.append_token(node, token)
        return node

    def tokens(self, node: int) -> tuple[int, ...]:
        answer: list[int] = []
        while node:
            answer.append(self.token[node])
            node = self.parent[node]
        return tuple(reversed(answer))
