"""Exact commuting-layer enumeration for bounded-local, state-dependent actions.

The system must satisfy the footprint/commutation contracts in article.tex.
No immediate inverse pruning and no physical-state-only memoization are used.
All transitions are pure: neither this module nor an exhausted search mutates
its input state. This is a research kernel, not an unknot recognizer.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from itertools import combinations
from typing import Any, Callable, Iterable, Protocol

@dataclass(frozen=True)
class Action:
    key: tuple[int, ...]
    footprint: frozenset[int]
    payload: Any = field(compare=False, hash=False, repr=False, default=None)

class System(Protocol):
    def actions(self, state: Any) -> Iterable[Action]: ...
    def apply(self, state: Any, action: Action) -> Any: ...
    def goal(self, state: Any) -> Any | None: ...

@dataclass
class Stats:
    enumerations: int = 0
    subset_trials: int = 0
    layers: int = 0
    moves: int = 0
    max_layer_width: int = 0

class SearchExhausted(RuntimeError):
    """A resource cap, never a proof that a knot is nontrivial."""

@dataclass(frozen=True)
class Witness:
    layers: tuple[tuple[Action, ...], ...]
    terminal: Any
    final_state: Any
    @property
    def length(self) -> int:
        return sum(map(len, self.layers))

def _check_int(value: int, name: str, minimum: int = 0) -> None:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")

def layered_traces(system: System, initial: Any, depth: int, *,
                   max_roots: int | None = None,
                   admissible: Callable[[Action], bool] | None = None,
                   check: Callable[[], None] | None = None,
                   max_trials: int | None = None, stats: Stats | None = None):
    """Yield every canonical legal layered trace of <=depth moves.

    Every nonfirst-layer action must meet the *previous layer*, not just the
    accumulated support. Same-layer actions have pairwise disjoint footprints.
    Yields (final_state, layers), excluding the empty trace. max_roots bounds
    the first layer. Resource exhaustion raises SearchExhausted.
    """
    _check_int(depth, "depth")
    if max_roots is not None:
        _check_int(max_roots, "max_roots")
    if max_trials is not None:
        _check_int(max_trials, "max_trials")
    if stats is None:
        stats = Stats()
    def poll():
        if check is not None:
            check()
    def choices(state, remaining, previous, root):
        poll()
        stats.enumerations += 1
        candidates = []
        seen = set()
        for a in system.actions(state):
            poll()
            if not a.footprint:
                raise ValueError("empty footprints are outside the theorem")
            if a.key in seen:
                raise ValueError("action keys are not unique in this state")
            seen.add(a.key)
            if admissible is not None and not admissible(a):
                continue
            if previous is not None and a.footprint.isdisjoint(previous):
                continue
            candidates.append(a)
        candidates.sort(key=lambda a: a.key)
        upper = min(remaining, len(candidates))
        if root and max_roots is not None:
            upper = min(upper, max_roots)
        for size in range(1, upper + 1):
            for layer in combinations(candidates, size):
                poll()
                if max_trials is not None and stats.subset_trials >= max_trials:
                    raise SearchExhausted("layer-subset trial allowance exhausted")
                stats.subset_trials += 1
                used = set()
                valid = True
                for a in layer:
                    if not used.isdisjoint(a.footprint):
                        valid = False
                        break
                    used.update(a.footprint)
                if valid:
                    yield layer, frozenset(used)
    if depth == 0 or max_roots == 0:
        return
    # Each frame holds a pure state and its own suspended subset iterator.
    stack = [(initial, (), depth, choices(initial, depth, None, True))]
    while stack:
        poll()
        state, history, remaining, iterator = stack[-1]
        item = next(iterator, None)
        if item is None:
            stack.pop()
            continue
        layer, support = item
        batch = getattr(system, "apply_layer", None)
        if batch is not None:
            poll()
            result = batch(state, layer)
            stats.moves += len(layer)
        else:
            result = state
            for a in layer:
                poll()
                result = system.apply(result, a)
                stats.moves += 1
        stats.layers += 1
        stats.max_layer_width = max(stats.max_layer_width, len(layer))
        new_history = history + (layer,)
        yield result, new_history
        rest = remaining - len(layer)
        if rest:
            stack.append((result, new_history, rest,
                          choices(result, rest, support, False)))

def find_layered(system: System, initial: Any, depth: int, **kwargs) -> Witness | None:
    """Return a replayable witness, or None after complete bounded exhaustion.

    None means NO BOUNDED UNLOCK only; SearchExhausted means UNKNOWN even for
    the bounded subproblem. An initial goal is a zero-length witness.
    """
    _check_int(depth, "depth")
    if kwargs.get("check") is not None:
        kwargs["check"]()
    terminal = system.goal(initial)
    if terminal is not None:
        return Witness((), terminal, initial)
    for state, layers in layered_traces(system, initial, depth, **kwargs):
        terminal = system.goal(state)
        if terminal is not None:
            return Witness(layers, terminal, state)
    return None

def normal_form(actions: list[Action]) -> tuple[tuple[Action, ...], ...]:
    """Occurrence-level Foata layering; footprints are those of the given trace."""
    levels: list[int] = []
    layers: list[list[Action]] = []
    for i, a in enumerate(actions):
        level = 1 + max((levels[j] for j in range(i)
                         if not a.footprint.isdisjoint(actions[j].footprint)), default=0)
        levels.append(level)
        while len(layers) < level:
            layers.append([])
        layers[level-1].append(a)
    return tuple(tuple(sorted(layer, key=lambda a: a.key)) for layer in layers)

def ancestor_cone(actions: list[Action], terminal_footprint: frozenset[int]):
    """Retain the backwards dependency cone of one local terminal predicate."""
    active = set(terminal_footprint)
    retained = []
    for a in reversed(actions):
        if not active.isdisjoint(a.footprint):
            retained.append(a)
            active.update(a.footprint)
    return list(reversed(retained)), frozenset(active)
