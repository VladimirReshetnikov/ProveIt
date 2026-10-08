"""Compile requested partitions to a merge trie and evaluate it exactly.

Compilation is optional: naturally ordered merge streams can use the cursor
API without rebuilding a plan. A trie can have Q*(b-1) edges in the worst case.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
from .linear import Budget, tick
from .terminal import blocks_from_labels

@dataclass(frozen=True)
class MergePlan:
    terminals: int
    events: tuple[tuple[int,int,int], ...]
    observations: tuple[int, ...]

    @classmethod
    def compile(cls, b: int, partitions: Sequence[Sequence[int]]) -> 'MergePlan':
        if type(b) is not int or b < 1:
            raise ValueError('positive terminal count required')
        events=[];observations=[];transitions={}
        for labels in partitions:
            groups=blocks_from_labels(labels,b);node=0
            for anchor in sorted(groups):
                for source in sorted(groups[anchor]-{anchor}):
                    key=(node,anchor,source)
                    if key not in transitions:
                        events.append(key);transitions[key]=len(events)
                    node=transitions[key]
            observations.append(node)
        return cls(b,tuple(events),tuple(observations))

    def evaluate(self, engine, budget: Budget | None = None) -> list[int]:
        """Accept TerminalKernel (field residues) or ExactObserver (integers).

        The entire call either returns its results or raises. Previously
        published engine/cursor objects are not mutated by failed updates.
        """
        b=engine.b if hasattr(engine,'b') else len(engine.terminals)
        if b!=self.terminals:raise ValueError('terminal count mismatch')
        tree=[[] for _ in range(len(self.events)+1)]
        for i,(parent,a,z) in enumerate(self.events,1):
            if not 0<=parent<i:raise ValueError('parents must precede children')
            tree[parent].append((i,a,z))
        if any(type(i) is not int or not 0<=i<len(tree) for i in self.observations):
            raise ValueError('invalid observation node')
        values=[0]*len(tree)
        def value(state):return state.residue if hasattr(state,'residue') else state.value
        root=engine.cursor(budget);values[0]=value(root)
        stack=[(root,iter(tree[0]))]
        while stack:
            tick(budget,1)
            state,it=stack[-1]
            edge=next(it,None)
            if edge is None:stack.pop();continue
            i,a,z=edge;child=state.merged(a,z,budget)
            values[i]=value(child);stack.append((child,iter(tree[i])))
        return [values[i] for i in self.observations]
