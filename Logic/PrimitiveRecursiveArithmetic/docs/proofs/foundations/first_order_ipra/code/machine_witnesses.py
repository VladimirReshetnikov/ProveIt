"""Check both finite-witness constructions in the computability chapter.

Input letters, instruction labels and structure elements are numbered from zero.
Stacks are tuples with their top at the left. The time-model format encodes a
state partition by giving one state label per time. Run directly for the tests.
"""
from dataclasses import dataclass, replace
from itertools import product


@dataclass(frozen=True)
class Push:
    stack: int  # zero is left, one is right
    letter: int
    jump: int


@dataclass(frozen=True)
class Pop:
    stack: int
    empty: int
    targets: tuple[int, ...]


@dataclass(frozen=True)
class Program:
    alphabet: int
    code: tuple[Push | Pop | None, ...]
    start: int
    yes: int
    no: int


Word = tuple[int, ...]
Config = tuple[int, Word, Word]


def require(test: bool, reason: str) -> None:
    if not test:
        raise ValueError(reason)


def step(p: Program, config: Config) -> Config:
    label, left, right = config
    inst = p.code[label]
    if inst is None:  # the two stopping labels (or an undefined self-loop)
        return config
    stacks = [left, right]
    source = stacks[inst.stack]
    if isinstance(inst, Push):
        stacks[inst.stack] = (inst.letter,) + source
        target = inst.jump
    elif source:
        stacks[inst.stack] = source[1:]
        target = inst.targets[source[0]]
    else:
        target = inst.empty
    return target, stacks[0], stacks[1]


def run(p: Program, word: Word, budget: int) -> list[Config]:
    trace = [(p.start, (), word)]
    for _ in range(budget):
        if trace[-1][0] in (p.yes, p.no):
            break
        trace.append(step(p, trace[-1]))
    return trace


def verify_trace(p: Program, word: Word, trace: list[Config], stop: int) -> None:
    require(bool(trace) and trace[0] == (p.start, (), word), "bad initial configuration")
    require(trace[-1][0] == stop, "wrong end label")
    for a, b in zip(trace, trace[1:]):
        require(a[0] not in (p.yes, p.no) and b == step(p, a), "invalid trace transition")


@dataclass(frozen=True)
class HornModel:
    empty: int
    cons: tuple[tuple[int, ...], ...]     # letter, suffix -> prefixed word
    facts: tuple[tuple[tuple[bool, ...], ...], ...]  # label, left, right
    yes_atom: bool


def rejecting_model(p: Program, word: Word, trace: list[Config]) -> HornModel:
    verify_trace(p, word, trace, p.no)
    bound = max(max(len(l), len(r)) for _, l, r in trace)
    words = [w for n in range(bound + 1) for w in product(range(p.alphabet), repeat=n)]
    numbers = {w: i for i, w in enumerate(words)}
    overflow = len(words)
    cons = tuple(tuple(numbers.get((a,) + w, overflow) for w in words) + (overflow,)
                 for a in range(p.alphabet))
    reached = {(i, numbers[l], numbers[r]) for i, l, r in trace}
    domain = range(overflow + 1)
    facts = tuple(tuple(tuple((i, l, r) in reached for r in domain) for l in domain)
                  for i in range(len(p.code)))
    return HornModel(numbers[()], cons, facts, False)


def verifies_countermodel(p: Program, word: Word, m: HornModel) -> bool:
    """Interpret every universal Horn matrix at every pair of domain values."""
    if not m.facts or len(m.facts) != len(p.code) or m.yes_atom:
        return False
    d = len(m.facts[0])
    if not 0 <= m.empty < d or len(m.cons) != p.alphabet:
        return False
    if any(len(t) != d or any(not 0 <= v < d for v in t) for t in m.cons):
        return False
    if any(len(tab) != d or any(len(row) != d for row in tab) for tab in m.facts):
        return False
    initial_right = m.empty
    for letter in reversed(word):
        initial_right = m.cons[letter][initial_right]
    if not m.facts[p.start][m.empty][initial_right]:
        return False
    for l, r in product(range(d), repeat=2):
        if m.facts[p.yes][l][r]:
            return False
        for i, inst in enumerate(p.code):
            if inst is None:
                continue
            # Other and suffix values exhaust the whole domain, including overflow.
            suffix, other = (l, r) if inst.stack == 0 else (r, l)

            def holds(label: int, own: int) -> bool:
                return (m.facts[label][own][other] if inst.stack == 0
                        else m.facts[label][other][own])

            if isinstance(inst, Push):
                if holds(i, suffix) and not holds(inst.jump, m.cons[inst.letter][suffix]):
                    return False
            else:
                if holds(i, m.empty) and not holds(inst.empty, m.empty):
                    return False
                for a, target in enumerate(inst.targets):
                    if holds(i, m.cons[a][suffix]) and not holds(target, suffix):
                        return False
    return True


@dataclass(frozen=True)
class TimeModel:
    nodes: int
    empty: int
    edges: frozenset[tuple[int, int, int]]  # letter, parent, child
    less: tuple[tuple[bool, ...], ...]
    states: tuple[int, ...]
    left: tuple[int, ...]
    right: tuple[int, ...]


def accepting_model(p: Program, word: Word, trace: list[Config]) -> TimeModel:
    verify_trace(p, word, trace, p.yes)
    words = {w[j:] for _, l, r in trace for w in (l, r) for j in range(len(w) + 1)}
    num = {w: i for i, w in enumerate(sorted(words, key=lambda w: (len(w), w)))}
    edges = frozenset((w[0], num[w[1:]], num[w]) for w in words if w)
    # Reverse numbering prevents the checker from silently assuming time order.
    records = list(reversed(trace))
    less = tuple(tuple(j < i for j in range(len(trace))) for i in range(len(trace)))
    return TimeModel(len(num), num[()], edges, less, tuple(i for i, _, _ in records),
                     tuple(num[l] for _, l, _ in records), tuple(num[r] for _, _, r in records))


def extract(p: Program, word: Word, m: TimeModel) -> list[Config]:
    """Validate the time, stack and transition axioms while extracting a run."""
    n = len(m.states)
    require(n > 0 and len(m.left) == n and len(m.right) == n, "time table dimensions")
    require(len(m.less) == n and all(len(row) == n for row in m.less), "order dimensions")
    require(all(0 <= i < len(p.code) for i in m.states), "state label")
    require(0 <= m.empty < m.nodes and all(0 <= x < m.nodes for x in m.left + m.right),
            "stack table range")
    times = range(n)
    for i, j in product(times, repeat=2):
        require((m.less[i][j] != m.less[j][i]) if i != j else not m.less[i][i], "order")
        for k in times:
            require(not (m.less[i][j] and m.less[j][k]) or m.less[i][k], "transitivity")
    ordered = sorted(times, key=lambda j: sum(m.less[i][j] for i in times))
    incoming = {}
    for a, x, z in m.edges:
        require(0 <= a < p.alphabet and 0 <= x < m.nodes and 0 <= z < m.nodes, "edge range")
        require(z != m.empty and z not in incoming, "invalid root or ambiguous incoming edge")
        incoming[z] = (a, x)
    first = ordered[0]
    require(m.states[first] == p.start and m.left[first] == m.empty, "initial label or left stack")
    z = m.right[first]
    chain = []
    for a in word:
        require(z in incoming and incoming[z][0] == a, "bad input chain")
        chain.append((a, z))
        z = incoming[z][1]
    require(z == m.empty and m.states[ordered[-1]] == p.yes, "bad endpoints")
    # Each stack stores (letter,vertex) pairs from the root towards its top.
    stacks = [[], list(reversed(chain))]
    trace = [(p.start, (), word)]
    for i, j in zip(ordered, ordered[1:]):
        ins = p.code[m.states[i]]
        require(ins is not None and m.states[i] not in (p.yes, p.no), "no legal instruction")
        tables = [m.left, m.right]
        top = tables[ins.stack]
        other = tables[1 - ins.stack]
        path = stacks[ins.stack]
        require(other[i] == other[j], "unchanged stack changed")
        require(top[i] == (path[-1][1] if path else m.empty), "path invariant")
        if isinstance(ins, Push):
            require((ins.letter, top[i], top[j]) in m.edges, "bad push edge")
            path.append((ins.letter, top[j]))
            target = ins.jump
        elif not path:
            require(top[j] == m.empty, "bad empty-pop case")
            target = ins.empty
        else:
            a, vertex = path.pop()
            before = path[-1][1] if path else m.empty
            require(incoming.get(vertex) == (a, before) and top[j] == before, "bad pop edge")
            target = ins.targets[a]
        require(target == m.states[j], "wrong destination")
        left, right = (tuple(a for a, _ in reversed(stack)) for stack in stacks)
        trace.append((target, left, right))
    return trace


def self_test() -> None:
    p = Program(2, (Pop(1, 4, (1, 4)), Push(0, 1, 2), Pop(0, 4, (4, 3)), None, None),
                0, 3, 4)
    for word in ((), (1,), (1, 0)):
        trace = run(p, word, 10)
        model = rejecting_model(p, word, trace)
        assert verifies_countermodel(p, word, model)
        assert not verifies_countermodel(p, word, replace(model, yes_atom=True))
    for word in ((0,), (0, 1), (0, 0, 1)):
        trace = run(p, word, 10)
        model = accepting_model(p, word, trace)
        assert extract(p, word, model) == trace
        bad_states = list(model.states)
        bad_states[1] = p.start
        try:
            extract(p, word, replace(model, states=tuple(bad_states)))
        except ValueError:
            pass
        else:
            raise AssertionError("malformed transition certificate accepted")
        try:
            accepting_model(p, word, [trace[0], trace[-1]])
        except ValueError:
            pass
        else:
            raise AssertionError("malformed trace accepted")
    # A legal model need not be the canonical word tree: permit a disjoint cycle.
    trace = run(p, (0,), 10)
    m = accepting_model(p, (0,), trace)
    cycle = replace(m, nodes=m.nodes + 1, edges=m.edges | {(0, m.nodes, m.nodes)})
    assert extract(p, (0,), cycle) == trace
    print("Validated three complete rejecting Horn models and rejected three corrupted models.")
    print("Recovered three accepting traces; rejected six malformed witnesses and ignored a disjoint cycle.")


if __name__ == "__main__":
    self_test()
