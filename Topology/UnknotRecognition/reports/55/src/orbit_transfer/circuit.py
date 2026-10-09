"""Value-independent, monotone orbit-transfer circuits with selective transpose.

A leaf denotes a constant weight on ONE source interval. Emitted expressions
are per-orbit values; their multiplicities must NOT scale a selected witness.
Compilation accepts only a source-bound, locally checked native AHT trace.
"""
from __future__ import annotations
from bisect import bisect_left
from dataclasses import dataclass
from typing import Callable, Iterable, Sequence
from .trace import CheckedTrace, check_trace, integer


class ResourceExhausted(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class Gate:
    kind: str
    left: int = 0
    right: int = 0
    factor: int = 0


@dataclass(frozen=True, slots=True)
class Emission:
    node: int
    multiplicity: int
    event: int


class Circuit:
    """A nonnegative integer linear DAG; signed input values remain supported."""
    def __init__(self, leaves: int, *, max_nodes: int | None = None,
                 check: Callable[[],None] | None = None):
        if type(leaves) is not int or leaves < 0:
            raise ValueError('leaves must be a nonnegative integer')
        if max_nodes is not None and (type(max_nodes) is not int or max_nodes < 0):
            raise ValueError('max_nodes must be a nonnegative integer or None')
        self.check = check if check is not None else lambda: None
        self.max_nodes = max_nodes
        self.leaves = leaves
        self.gates = [Gate('zero')]
        self.cache: dict[tuple,int] = {}
        self._add_gate_budget()
        for j in range(leaves):
            self._append(Gate('input',factor=j))

    def _add_gate_budget(self):
        self.check()
        if self.max_nodes is not None and len(self.gates) > self.max_nodes:
            raise ResourceExhausted('circuit-node allowance exhausted')

    def _append(self, gate: Gate) -> int:
        self.check()
        if self.max_nodes is not None and len(self.gates) >= self.max_nodes:
            raise ResourceExhausted('circuit-node allowance exhausted')
        self.gates.append(gate)
        return len(self.gates)-1

    def scale(self, node: int, factor: int) -> int:
        if type(factor) is not int or factor < 0:
            raise ValueError('circuit coefficients must be nonnegative integers')
        if not node or not factor:
            return 0
        if factor == 1:
            return node
        key = ('scale',node,factor)
        if key not in self.cache:
            self.cache[key] = self._append(Gate('scale',node,factor=factor))
        return self.cache[key]

    def add(self, a: int, b: int) -> int:
        if not a: return b
        if not b: return a
        if a == b: return self.scale(a,2)
        a,b = sorted((a,b))
        key = ('add',a,b)
        if key not in self.cache:
            self.cache[key] = self._append(Gate('add',a,b))
        return self.cache[key]

    def evaluate(self, inputs: Sequence[int]) -> list[int]:
        if len(inputs) != self.leaves or any(type(x) is not int for x in inputs):
            raise ValueError('one integer value per source interval is required')
        values = [0]*len(self.gates)
        for i,g in enumerate(self.gates):
            self.check()
            if g.kind == 'input': values[i] = inputs[g.factor]
            elif g.kind == 'add': values[i] = values[g.left]+values[g.right]
            elif g.kind == 'scale': values[i] = g.factor*values[g.left]
        return values

    def transpose(self, seeds: Iterable[tuple[int,int]]) -> list[int]:
        """Return input coefficients of the specified linear combination of outputs.

        A single representative uses (emission.node, 1), not multiplicity.
        Several seeds can instead request exact aggregate source counts.
        """
        adjoint = [0]*len(self.gates)
        for node,coefficient in seeds:
            if type(node) is not int or not 0 <= node < len(adjoint):
                raise ValueError('invalid circuit seed node')
            if type(coefficient) is not int:
                raise ValueError('seed coefficients must be integers')
            adjoint[node] += coefficient
        for i in range(len(self.gates)-1,0,-1):
            self.check()
            a,g = adjoint[i],self.gates[i]
            if not a: continue
            if g.kind == 'add':
                adjoint[g.left] += a; adjoint[g.right] += a
            elif g.kind == 'scale':
                adjoint[g.left] += g.factor*a
        return adjoint[1:self.leaves+1]


def _append(runs: list[tuple], lo: int, hi: int, node: int):
    if lo == hi: return
    if runs and runs[-1][1] == lo and runs[-1][2] == node:
        runs[-1] = (runs[-1][0],hi,node)
    else:
        runs.append((lo,hi,node))


def _positive_sweep(size: int, pieces: list[tuple], circuit: Circuit) -> list[tuple]:
    """Persistent-expression segment tree: no subtraction or value comparisons.

    Each geometric contribution occupies one temporary leaf. At a breakpoint,
    ending pieces are removed before starting pieces are activated.
    """
    if not size: return []
    pieces = [(lo,hi,node) for lo,hi,node in pieces if lo < hi and node]
    if not pieces: return [(0,size,0)]
    width = 1 << (len(pieces)-1).bit_length()
    tree = [0]*(2*width)
    starts: dict[int,list[int]] = {}; ends: dict[int,list[int]] = {}
    for j,(lo,hi,node) in enumerate(pieces):
        circuit.check()
        if not 0 <= lo < hi <= size:
            raise ArithmeticError('transported interval leaves surviving universe')
        starts.setdefault(lo,[]).append(j); ends.setdefault(hi,[]).append(j)
    points = sorted(set(starts)|set(ends)|{0,size})
    def update(j,value):
        k = width+j; tree[k] = value
        k //= 2
        while k:
            tree[k] = circuit.add(tree[2*k],tree[2*k+1]); k //= 2
    runs = []
    for lo,hi in zip(points,points[1:]):
        circuit.check()
        for j in ends.get(lo,()): update(j,0)
        for j in starts.get(lo,()): update(j,pieces[j][2])
        _append(runs,lo,hi,tree[1])
    return runs


def _fold(runs: list[tuple], event, circuit: Circuit) -> list[tuple]:
    size,cut = event.old_size,event.new_size
    pieces = []
    for lo,hi,node in runs:
        circuit.check()
        if lo < cut: pieces.append((lo,min(hi,cut),node))
        left = max(lo,cut)
        if left >= hi: continue
        if event.kind == 'translation':
            period = event.parameter; base = cut-period
            q,r = divmod(hi-left,period)
            if q: pieces.append((base,cut,circuit.scale(node,q)))
            start = base+(left-base)%period
            first = min(r,cut-start)
            if first: pieces.append((start,start+first,node))
            if r > first: pieces.append((base,base+r-first,node))
        else:
            a = event.parameter
            pieces.append((a+size-hi,a+size-left,node))
    return _positive_sweep(cut,pieces,circuit)


def _contract(runs: list[tuple], event, event_index: int,
              outputs: list[Emission], circuit: Circuit) -> list[tuple]:
    if not runs: return []
    points = sorted({0,event.old_size}
                    |{p for lo,hi,_ in runs for p in (lo,hi)}
                    |{p for lo,hi in event.gaps for p in (lo,hi)})
    i=j=removed=0; result=[]
    for lo,hi in zip(points,points[1:]):
        circuit.check()
        while runs[i][1] <= lo: i += 1
        while j < len(event.gaps) and event.gaps[j][1] <= lo: j += 1
        node = runs[i][2]
        if j < len(event.gaps) and event.gaps[j][0] <= lo:
            outputs.append(Emission(node,hi-lo,event_index)); removed += hi-lo
        else:
            _append(result,lo-removed,hi-removed,node)
    return result


@dataclass
class TransferProgram:
    size: int
    cuts: tuple[int,...]
    circuit: Circuit
    emissions: tuple[Emission,...]
    orbit_count: int
    stats: dict[str,int]

    def values_on_atoms(self, intervals: Iterable[tuple[int,int,int]]) -> list[int]:
        """Prepare an additive scalar query; new endpoints require recompilation."""
        delta = [0]*len(self.cuts)
        for lo,hi,value in intervals:
            self.circuit.check()
            lo,hi,value = integer(lo),integer(hi),integer(value)
            if not 0 <= lo <= hi <= self.size:
                raise ValueError('query interval outside source')
            if lo == hi: continue
            left,right = bisect_left(self.cuts,lo),bisect_left(self.cuts,hi)
            if left == len(self.cuts) or right == len(self.cuts) or self.cuts[left] != lo or self.cuts[right] != hi:
                raise ValueError('query introduces a new source cut: recompile')
            delta[left] += value; delta[right] -= value
        answer=[]; value=0
        for event in delta[:-1]:
            self.circuit.check(); value += event; answer.append(value)
        return answer

    def evaluate_intervals(self, intervals: Iterable[tuple[int,int,int]]) -> list[int]:
        values = self.circuit.evaluate(self.values_on_atoms(intervals))
        return [values[e.node] for e in self.emissions]

    def histogram(self, queries: Sequence[Sequence[tuple]]) -> list[dict]:
        columns = [self.evaluate_intervals(query) for query in queries]
        histogram={}
        for j,e in enumerate(self.emissions):
            self.circuit.check()
            vector=tuple(col[j] for col in columns)
            histogram[vector]=histogram.get(vector,0)+e.multiplicity
        return [{'weight':list(key),'orbits':value} for key,value in sorted(histogram.items())]

    def extract(self, emission_index: int, coordinates: Iterable[tuple[int,int,int]],
                dimension: int) -> list[int]:
        """Extract one representative's coordinates from interval-ownership rows.

        ``coordinates`` contains (coordinate_index, start, stop). Overlapping
        rows are additive, and multiple rows per coordinate are permitted.
        """
        if type(emission_index) is not int or not 0 <= emission_index < len(self.emissions):
            raise ValueError('invalid emission index')
        if type(dimension) is not int or dimension < 0:
            raise ValueError('dimension must be a nonnegative integer')
        coefficients=self.circuit.transpose([(self.emissions[emission_index].node,1)])
        prefix=[0]
        for value in coefficients:
            self.circuit.check(); prefix.append(prefix[-1]+value)
        result=[0]*dimension
        for coordinate,lo,hi in coordinates:
            self.circuit.check()
            coordinate,lo,hi=integer(coordinate),integer(lo),integer(hi)
            if not 0 <= coordinate < dimension or not 0 <= lo <= hi <= self.size:
                raise ValueError('invalid coordinate-ownership interval')
            left,right=bisect_left(self.cuts,lo),bisect_left(self.cuts,hi)
            if right == len(self.cuts) or self.cuts[left] != lo or self.cuts[right] != hi:
                raise ValueError('ownership introduces a new cut: recompile')
            result[coordinate] += prefix[right]-prefix[left]
        return result


def compile_transfer(size: int, pairings: Iterable, proof: dict,
                     cuts: Iterable[int], *, max_nodes: int | None = None,
                     check: Callable[[],None] | None = None) -> TransferProgram:
    """Compile a complete source-bound trace. No point universe is expanded."""
    poll=check if check is not None else lambda: None
    if max_nodes is not None and (type(max_nodes) is not int or max_nodes < 0):
        raise ValueError('max_nodes must be a nonnegative integer or None')
    checked=check_trace(size,pairings,proof,poll)
    partition=sorted({integer(x) for x in cuts}|{0,checked.size})
    if partition[0] < 0 or partition[-1] > checked.size:
        raise ValueError('source cut outside universe')
    circuit=Circuit(len(partition)-1,max_nodes=max_nodes,check=poll)
    runs=[(lo,hi,j+1) for j,(lo,hi) in enumerate(zip(partition,partition[1:]))]
    outputs=[]; peak=len(runs); visits=0; folds=0
    for j,event in enumerate(checked.operations):
        poll(); visits += len(runs)
        if event.kind == 'contract':
            runs=_contract(runs,event,j,outputs,circuit)
        else:
            runs=_fold(runs,event,circuit); folds += 1
        peak=max(peak,len(runs))
    if runs or sum(e.multiplicity for e in outputs) != checked.orbit_count:
        raise ArithmeticError('compiled transfer did not exhaust source')
    stats=dict(source_atoms=len(partition)-1, source_events=checked.source_events,
               transport_events=len(checked.operations),folds=folds,
               peak_runs=peak,run_visits=visits,circuit_nodes=len(circuit.gates),
               emissions=len(outputs),input_bits=checked.size.bit_length())
    return TransferProgram(checked.size,tuple(partition),circuit,tuple(outputs),
                           checked.orbit_count,stats)
