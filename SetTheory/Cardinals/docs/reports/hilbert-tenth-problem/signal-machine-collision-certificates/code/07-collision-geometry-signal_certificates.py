"""Exact, event-sparse chamber certificates for rational signal machines.

Python 3.10+, standard library only.  All geometry uses Fraction.  A skeleton is
an ordered sequence of batches; each batch consists of disjoint, left-to-right
contiguous tuples of live signal IDs.  IDs are assigned initially left-to-right,
then by batch, collision site, and increasing outgoing speed.

This is an executable research implementation, not a proof-assistant artifact.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, lcm
from types import MappingProxyType
from typing import Iterable, Mapping, Sequence

Form = tuple[F, ...]
Group = tuple[int, ...]
Batch = tuple[Group, ...]
Skeleton = tuple[Batch, ...]

class InvalidSkeleton(ValueError):
    """The discrete proposal is ill-formed or immediately unrealizable."""


def add(a: Form, b: Form) -> Form:
    return tuple(x + y for x, y in zip(a, b))


def sub(a: Form, b: Form) -> Form:
    return tuple(x - y for x, y in zip(a, b))


def mul(c: F | int, a: Form) -> Form:
    return tuple(c * x for x in a)


def dot(a: Sequence, b: Sequence):
    if len(a) != len(b):
        raise ValueError("dimension mismatch")
    return sum((x*y for x,y in zip(a,b)), F(0))


def primitive(a: Form, equality: bool) -> tuple[int, ...]:
    den = lcm(*(x.denominator for x in a)) if a else 1
    row = tuple(int(x * den) for x in a)
    common = 0
    for x in row:
        common = gcd(common, abs(x))
    if common:
        row = tuple(x // common for x in row)
    # A positive scaling is essential for inequalities.
    if equality and next((x for x in row if x), 0) < 0:
        row = tuple(-x for x in row)
    return row


@dataclass(frozen=True)
class Machine:
    speeds: Mapping[str, F]
    rules: Mapping[frozenset[str], tuple[str, ...]]
    transparent_default: bool = True

    def __post_init__(self):
        speeds = {str(k): F(v) for k,v in self.speeds.items()}
        if not speeds:
            raise ValueError("at least one signal type is required")
        normalized = {}
        for raw_in, raw_out in self.rules.items():
            incoming = frozenset(raw_in)
            outgoing = tuple(raw_out)
            if len(incoming) < 2:
                raise ValueError("a collision needs at least two inputs")
            if not incoming <= speeds.keys() or any(x not in speeds for x in outgoing):
                raise ValueError("unknown signal type in a rule")
            if len({speeds[x] for x in incoming}) != len(incoming):
                raise ValueError("incoming speeds must be distinct")
            if len({speeds[x] for x in outgoing}) != len(outgoing):
                raise ValueError("outgoing speeds must be distinct")
            normalized[incoming] = tuple(sorted(outgoing, key=speeds.__getitem__))
        object.__setattr__(self, 'speeds', MappingProxyType(speeds))
        object.__setattr__(self, 'rules', MappingProxyType(normalized))

    def outputs(self, labels: Sequence[str]) -> tuple[str, ...]:
        if len(labels) < 2 or len(set(labels)) != len(labels):
            raise InvalidSkeleton("repeated type or too few inputs")
        try:
            vv = [self.speeds[x] for x in labels]
        except KeyError as exc:
            raise InvalidSkeleton("unknown signal type") from exc
        if len(set(vv)) != len(vv):
            raise InvalidSkeleton("parallel incoming signals cannot collide")
        key = frozenset(labels)
        if key in self.rules:
            return self.rules[key]
        if self.transparent_default:
            return tuple(sorted(labels, key=self.speeds.__getitem__))
        raise InvalidSkeleton("undefined collision rule")


@dataclass(frozen=True)
class Certificate:
    dimension: int
    equalities: tuple[tuple[int, ...], ...]
    strict: tuple[tuple[int, ...], ...]
    times: tuple[Form, ...]
    event_times: tuple[Form, ...]
    event_positions: tuple[Form, ...]
    depths: tuple[int, ...]
    intervals: int
    raw_rows: int
    event_count: int
    batch_count: int
    row_bound: int

    def accepts(self, gaps: Sequence[int | F]) -> bool:
        if len(gaps) != self.dimension:
            raise ValueError("wrong number of initial gaps")
        return (all(dot(a,gaps) == 0 for a in self.equalities)
                and all(dot(a,gaps) > 0 for a in self.strict))

    def witnesses(self, gaps: Sequence[int]) -> tuple[int, ...]:
        if any(type(x) is not int or x < 0 for x in gaps):
            raise ValueError("Diophantine parameters must be natural integers")
        if not self.accepts(gaps):
            raise ValueError("parameters do not realize this skeleton")
        return tuple(int(dot(a,gaps)) - 1 for a in self.strict)

    def evaluate(self, gaps: Sequence[int], witnesses: Sequence[int]) -> int:
        if len(witnesses) != len(self.strict) or len(gaps) != self.dimension:
            raise ValueError("wrong parameter or witness dimension")
        if any(type(x) is not int or x < 0 for x in (*gaps,*witnesses)):
            raise ValueError("all parameters and witnesses must be natural integers")
        ans = sum(int(dot(a,gaps))**2 for a in self.equalities)
        ans += sum((int(dot(a,gaps))-1-z)**2 for a,z in zip(self.strict,witnesses))
        return ans

    def to_dict(self):
        def rows(xs): return [[str(v) for v in row] for row in xs]
        return dict(dimension=self.dimension, equalities=self.equalities,
                    strict=self.strict, times=rows(self.times),
                    event_times=rows(self.event_times),
                    event_positions=rows(self.event_positions), depths=self.depths,
                    intervals=self.intervals, raw_rows=self.raw_rows,
                    event_count=self.event_count, batch_count=self.batch_count,
                    row_bound=self.row_bound,
                    polynomial="sum((E_i*g)^2)+sum((G_j*g-1-z_j)^2)",
                    domain="g,z in nonnegative integers")


def compile_skeleton(machine: Machine, initial: Sequence[str],
                     skeleton: Sequence[Sequence[Sequence[int]]]) -> Certificate:
    initial = tuple(initial)
    if len(initial) < 2:
        raise ValueError("compiler interface requires at least two initial signals")
    if any(x not in machine.speeds for x in initial):
        raise ValueError("unknown initial signal type")
    d = len(initial)-1
    zero = (F(0),)*d
    labels = dict(enumerate(initial))
    intercepts = {i: tuple(F(int(j<i)) for j in range(d)) for i in range(len(initial))}
    live = list(range(len(initial)))
    births = {i: (0,-1-i) for i in live}
    deaths: dict[int, tuple[int,int]] = {}
    sigdepth = {i:0 for i in live}
    next_id = len(live)
    times = [zero]
    event_times, event_positions, depths = [], [], []
    eq: list[Form] = []
    gt: list[Form] = [tuple(F(int(i==j)) for i in range(d)) for j in range(d)]
    open_pairs = {(a,b):0 for a,b in zip(live,live[1:])}
    intervals = []
    E = 0
    input_count = 0
    output_count = 0
    B = len(skeleton)
    for k, raw_batch in enumerate(skeleton, 1):
        if not raw_batch:
            raise InvalidSkeleton("empty batch")
        groups = [tuple(g) for g in raw_batch]
        index = {sid:i for i,sid in enumerate(live)}
        previous_end = -1
        event_data = []
        for group in groups:
            if len(group)<2 or len(set(group)) != len(group):
                raise InvalidSkeleton("invalid input group")
            if any(s not in index for s in group):
                raise InvalidSkeleton("input signal is not alive")
            start = index[group[0]]
            if tuple(live[start:start+len(group)]) != group or start<=previous_end:
                raise InvalidSkeleton("groups must be contiguous, disjoint, and left-to-right")
            previous_end = start+len(group)-1
            incoming = [labels[s] for s in group]
            v = [machine.speeds[x] for x in incoming]
            if any(x<=y for x,y in zip(v,v[1:])):
                raise InvalidSkeleton("incoming speeds must decrease from left to right")
            outgoing = machine.outputs(incoming)
            s,t = group[:2]
            te = mul(1/(v[0]-v[1]), sub(intercepts[t],intercepts[s]))
            xe = add(intercepts[s],mul(v[0],te))
            for sid in group[2:]:
                eq.append(sub(add(intercepts[sid],mul(machine.speeds[labels[sid]],te)),xe))
            dep = 1+max(sigdepth[sid] for sid in group)
            event_times.append(te); event_positions.append(xe); depths.append(dep)
            eid = E
            E += 1
            input_count += len(group)
            output_count += len(outgoing)
            for sid in group:
                deaths[sid]=(k,eid)
            event_data.append((start,group,outgoing,te,xe,eid,dep))
        tk = event_data[0][3]
        gt.append(sub(tk,times[-1]))
        for item in event_data[1:]:
            eq.append(sub(item[3],tk))
        times.append(tk)
        new_live = []
        cursor = 0
        for start, group, outgoing, te, xe, eid, dep in event_data:
            new_live.extend(live[cursor:start])
            for label in outgoing:
                sid=next_id; next_id+=1
                labels[sid]=label
                intercepts[sid]=sub(xe,mul(machine.speeds[label],te))
                births[sid]=(k,eid); sigdepth[sid]=dep
                new_live.append(sid)
            cursor=start+len(group)
        new_live.extend(live[cursor:])
        new_pairs=set(zip(new_live,new_live[1:]))
        for pair in sorted(set(open_pairs)-new_pairs):
            intervals.append((pair,open_pairs.pop(pair),k))
        for pair in sorted(new_pairs-set(open_pairs)):
            open_pairs[pair]=k
        live=new_live
    for pair,start in sorted(open_pairs.items()):
        if start<B:
            intervals.append((pair,start,B))
    for (left,right),start,end in intervals:
        zstart=(births[left]==births[right] and births[left][0]==start)
        zend=(left in deaths and right in deaths and
              deaths[left]==deaths[right] and deaths[left][0]==end)
        if zstart and zend:
            raise InvalidSkeleton("distinct straight signals cannot separate then reunite")
        slope=machine.speeds[labels[right]]-machine.speeds[labels[left]]
        base=sub(intercepts[right],intercepts[left])
        for boundary,is_zero in ((start,zstart),(end,zend)):
            gap=add(base,mul(slope,times[boundary]))
            (eq if is_zero else gt).append(gap)
    raw_rows=len(eq)+len(gt)
    def canonical(forms, equality):
        result=set()
        for form in forms:
            row=primitive(form,equality)
            if not any(row):
                if not equality:
                    raise InvalidSkeleton("a strict separation is identically zero")
            else:
                result.add(row)
        return tuple(sorted(result))
    equalities=canonical(eq,True)
    strict=canonical(gt,False)
    m=len(set(machine.speeds.values()))
    bound=3*d+(3*m+1)*E
    if raw_rows>bound:
        raise AssertionError("internal row-bound failure")
    if len(intervals)>d+output_count+E:
        raise AssertionError("internal adjacency-bound failure")
    return Certificate(d,equalities,strict,tuple(times[1:]),tuple(event_times),
                       tuple(event_positions),tuple(depths),len(intervals),raw_rows,
                       E,B,bound)


@dataclass(frozen=True)
class SimulatedRun:
    skeleton: Skeleton
    times: tuple[F, ...]
    sites: tuple[tuple[F, ...], ...]
    stopped: bool


def simulate(machine: Machine, initial: Sequence[str], gaps: Sequence[int | F],
             max_batches: int = 20) -> SimulatedRun:
    """Independent all-pairs rational event simulator (no symbolic chambers)."""
    if max_batches<0 or len(initial)!=len(gaps)+1 or not initial:
        raise ValueError("invalid simulator dimensions or horizon")
    if any(F(g)<=0 for g in gaps) or any(x not in machine.speeds for x in initial):
        raise ValueError("positive gaps and known labels are required")
    pos=[F(0)]
    for g in gaps: pos.append(pos[-1]+F(g))
    live=[(i,label,x) for i,(label,x) in enumerate(zip(initial,pos))]
    next_id=len(live); clock=F(0)
    batches=[]; times=[]; sites=[]
    for _ in range(max_batches):
        candidates=[]
        for i,(_,left,x) in enumerate(live):
            for _,right,y in live[i+1:]:
                closing=machine.speeds[left]-machine.speeds[right]
                if closing>0:
                    delay=(y-x)/closing
                    if delay<=0:
                        raise ValueError("invalid right-limit order")
                    candidates.append(delay)
        if not candidates:
            return SimulatedRun(tuple(batches),tuple(times),tuple(sites),True)
        delay=min(candidates); clock+=delay
        moved=[(sid,label,x+machine.speeds[label]*delay) for sid,label,x in live]
        groups=[]; locs=[]; new_live=[]
        i=0
        while i<len(moved):
            j=i+1
            while j<len(moved) and moved[j][2]==moved[i][2]: j+=1
            block=moved[i:j]
            if len(block)==1:
                new_live.extend(block)
            else:
                groups.append(tuple(s for s,_,_ in block)); locs.append(block[0][2])
                out=machine.outputs([label for _,label,_ in block])
                for label in out:
                    new_live.append((next_id,label,block[0][2])); next_id+=1
            i=j
        if not groups:
            raise AssertionError("event selector found no collision")
        batches.append(tuple(groups)); times.append(clock); sites.append(tuple(locs))
        live=new_live
    return SimulatedRun(tuple(batches),tuple(times),tuple(sites),False)

@dataclass(frozen=True)
class UnionCertificate:
    """Quartic for a finite family of chambers of the same seed dimension.

    For disjoint chambers (e.g. canonical first-acceptance skeletons), every
    accepted seed has a unique full selector/slack tuple. Disjointness is a
    mathematical precondition for that uniqueness claim, not checked globally
    by this constructor. witnesses() detects overlap at its supplied seed.
    """
    certificates: tuple[Certificate, ...]

    def __post_init__(self):
        certs = tuple(self.certificates)
        if not certs:
            raise ValueError("use the constant polynomial 1 for an empty family")
        if len({c.dimension for c in certs}) != 1:
            raise ValueError("all chambers must have the same seed dimension")
        object.__setattr__(self, 'certificates', certs)

    def witnesses(self, gaps: Sequence[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
        hits = [k for k,c in enumerate(self.certificates) if c.accepts(gaps)]
        if not hits:
            raise ValueError("seed is not in the union")
        if len(hits) != 1:
            raise ValueError("overlapping chambers: uniqueness precondition fails")
        hit = hits[0]
        selectors = tuple(int(k == hit) for k in range(len(self.certificates)))
        slacks = tuple(z for k,c in enumerate(self.certificates)
                       for z in (c.witnesses(gaps) if k == hit else (0,)*len(c.strict)))
        return selectors, slacks

    def evaluate(self, gaps: Sequence[int], selectors: Sequence[int],
                 slacks: Sequence[int]) -> int:
        if len(gaps) != self.certificates[0].dimension:
            raise ValueError("wrong seed dimension")
        if len(selectors) != len(self.certificates):
            raise ValueError("wrong selector dimension")
        if len(slacks) != sum(len(c.strict) for c in self.certificates):
            raise ValueError("wrong slack dimension")
        if any(type(x) is not int or x < 0 for x in (*gaps,*selectors,*slacks)):
            raise ValueError("all variables must be nonnegative integers")
        total = (sum(selectors)-1)**2
        offset = 0
        for b,c in zip(selectors,self.certificates):
            total += sum((b*int(dot(a,gaps)))**2 for a in c.equalities)
            for a in c.strict:
                total += (b*(int(dot(a,gaps))-1)-slacks[offset])**2
                offset += 1
        return total

    def to_dict(self):
        return {
            'degree_bound': 4,
            'domain': 'g,selectors,slacks in nonnegative integers',
            'polynomial': '(sum(b)-1)^2 + sum_k,i (b_k E_ki*g)^2 '
                          '+ sum_k,j (b_k*(G_kj*g-1)-z_kj)^2',
            'uniqueness_condition': 'the constituent seed chambers are disjoint',
            'certificates': [c.to_dict() for c in self.certificates],
        }
