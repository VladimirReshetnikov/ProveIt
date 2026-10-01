#!/usr/bin/env python3
"""A name-equivariant two-stack heap machine and its scalar memory log.

Heap nodes have fields (symbol,next). Pointer 0 is null; node IDs are fresh.
Natural scalar addresses 2*node and 2*node+1 are a compiler representation,
not operations available to the source machine. Garbage is never reused.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from memory_quartic import Event


@dataclass
class PointerStacks:
    heads: list[int] = field(default_factory=lambda: [0, 0])
    nodes: dict[int, tuple[int, int]] = field(default_factory=dict)
    events: list[Event] = field(default_factory=list)
    births: list[int] = field(default_factory=list)
    actions: list[tuple] = field(default_factory=list)

    def push(self, stack: int, symbol: int, fresh: int | None = None) -> int:
        if stack not in (0, 1) or not isinstance(symbol, int) or symbol < 0:
            raise ValueError("invalid stack or symbol")
        node = len(self.births) + 1 if fresh is None else fresh
        if not isinstance(node, int) or node <= 0 or node in self.nodes:
            raise ValueError("allocation must use a never-before-used positive ID")
        tail = self.heads[stack]
        self.nodes[node] = (symbol, tail)
        self.births.append(node)
        self.events.extend((Event(2*node, 1, symbol), Event(2*node+1, 1, tail)))
        self.heads[stack] = node
        self.actions.append(("push", stack, symbol, node, tail))
        return node

    def pop(self, stack: int) -> int | None:
        if stack not in (0, 1):
            raise ValueError("invalid stack")
        node = self.heads[stack]
        if not node:
            self.actions.append(("empty", stack))
            return None
        symbol, tail = self.nodes[node]
        self.events.extend((Event(2*node, 0, symbol), Event(2*node+1, 0, tail)))
        self.heads[stack] = tail
        self.actions.append(("pop", stack, symbol, node, tail))
        return symbol

    def normalize(self) -> list[tuple]:
        names = {0: 0, **{v: i+1 for i, v in enumerate(self.births)}}
        return [(a[0], a[1]) if a[0] == "empty" else
                (a[0], a[1], a[2], names[a[3]], names[a[4]])
                for a in self.actions]
