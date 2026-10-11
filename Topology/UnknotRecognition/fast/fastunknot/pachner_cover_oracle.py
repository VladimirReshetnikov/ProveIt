"""Exact on-demand completion of an original footprint to a permitted cover.

Search only sets whose every component touches the supplied footprint.
Extraneous components can be deleted from any covering witness. Canonical
reverse search avoids duplicate extensions and does not materialize the
whole ambient region family. A capped completion is unknown, never False.
"""
from dataclasses import dataclass

from .normal_cocycle import CocycleLimit


def _components(graph,vertices,check):
    remaining=set(vertices);result=[]
    while remaining:
        check();root=min(remaining);remaining.remove(root);reached={root};pending=[root]
        while pending:
            check();v=pending.pop()
            for neighbour in graph[v]:
                if neighbour in remaining:
                    remaining.remove(neighbour);reached.add(neighbour);pending.append(neighbour)
        result.append(frozenset(reached))
    return result


def _rooted(graph,vertices,roots,check):
    return all(component & roots for component in _components(graph,vertices,check))


def _parent(graph,vertices,roots,check):
    for v in sorted(vertices-roots,reverse=True):
        check();candidate=vertices-{v}
        if _rooted(graph,candidate,roots,check):return candidate
    raise ArithmeticError('a rooted extension has no removable non-root vertex')


@dataclass(frozen=True)
class _FootprintState:
    consumed:frozenset
    region:tuple


class _CoverOracle:
    """Admit the existential cover language; witnesses do not constrain growth."""
    def __init__(self,graph,maximum,components,max_states=None):
        self.graph=graph;self.maximum=min(maximum,len(graph));self.components=components
        self.max_states=max_states;self.cache={}

    def complete(self,footprint,stats,check):
        check();stats['oracle_queries']+=1
        if footprint in self.cache:
            stats['oracle_cache_hits']+=1
            return self.cache[footprint]
        if len(footprint)>self.maximum:
            self.cache[footprint]=None;return None
        if len(_components(self.graph,footprint,check))<=self.components:
            result=tuple(sorted(footprint));self.cache[footprint]=result;return result
        if not self.components or len(footprint)==self.maximum:
            self.cache[footprint]=None;return None
        # Each minimal witness component intersects the footprint, and can
        # be grown from those roots. At most R vertices and four ports per
        # vertex give 2^O(R) possible rooted sets, independent of ambient t.
        stack=[footprint]
        while stack:
            check()
            if self.max_states is not None and stats['oracle_states']>=self.max_states:
                raise CocycleLimit('cover completion allowance exhausted')
            current=stack.pop();stats['oracle_states']+=1
            if len(_components(self.graph,current,check))<=self.components:
                result=tuple(sorted(current));self.cache[footprint]=result;return result
            if len(current)>=self.maximum:continue
            frontier={v for u in current for v in self.graph[u]}-current
            for v in sorted(frontier,reverse=True):
                check();child=current|{v}
                if _parent(self.graph,child,footprint,check)==current:stack.append(child)
        self.cache[footprint]=None
        return None

    def extend(self,state,consumed,stats,check):
        if state is False:
            check();return False
        footprint=(frozenset()if state is None else state.consumed)|consumed
        region=self.complete(footprint,stats,check)
        return False if region is None else _FootprintState(footprint,region)

    def witness(self,state):
        return ()if state is None else state.region
