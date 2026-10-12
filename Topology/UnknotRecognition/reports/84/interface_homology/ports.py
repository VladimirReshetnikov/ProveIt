"""Bounded marked-port reconstruction, downstream of a VERIFIED vertex query.

Input equivalences and core paths are assumed to come from source replay.
Neither this module nor a histogram by itself authenticates that geometric
claim. Relative boundary orientations of an orientable base are also a
source obligation; local consistency is checked here, not manufactured.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from .model import Model, Core, Surface, Loop, validate


@dataclass(frozen=True)
class Port:
    surface: int
    ends: tuple[int, int]  # quotient-vertex class labels
    start: int  # core vertex at the first endpoint
    word: tuple[int, ...] = ()  # open path along the central line of the rectangle
    orientation: int = 1  # base boundary direction on orientable bases


def endpoint_partition(port_count: int, histogram: tuple[tuple[int, int], ...]) -> tuple[int, ...]:
    """Decode (orbit-weight mask, orbit multiplicity) from a marked query.

    Endpoint j has the unique mark 2**j, for 0 <= j < 2*port_count.
    Each nonzero orbit weight must occur once; unmarked orbits may be numerous.
    Returned labels are dense and ordered by each class's least endpoint.
    """
    if type(port_count) is not int or port_count < 0:
        raise ValueError('invalid port count')
    all_bits = (1 << (2*port_count)) - 1
    masks = []
    seen = 0
    for mask, multiplicity in histogram:
        if type(mask) is not int or mask < 0 or type(multiplicity) is not int or multiplicity < 1:
            raise ValueError('invalid marked histogram entry')
        if not mask: continue
        if multiplicity != 1 or mask & ~all_bits or mask & seen:
            raise ValueError('duplicated or out-of-range endpoint marks')
        seen |= mask; masks.append(mask)
    if seen != all_bits:
        raise ValueError('missing marked endpoint')
    masks.sort(key=lambda mask: (mask & -mask).bit_length())
    labels = [-1] * (2*port_count)
    for i, mask in enumerate(masks):
        while mask:
            bit = mask & -mask
            labels[bit.bit_length()-1] = i
            mask -= bit
    return tuple(labels)


def assemble_interfaces(core: Core, bases: tuple[Surface, ...], ports: tuple[Port, ...]) -> Model:
    """Assemble A-components and circle words without expanding any base.

    `bases` must not already contain attachments. This consumes an explicit
    O(p)-size port graph, not the potentially huge base polygon complex.
    """
    validate(Model(core, bases))
    if any(s.attached for s in bases):
        raise ValueError('base templates already have attachments')
    owners = {}
    core_vertex = {}
    adjacency = {}
    for i, p in enumerate(ports):
        if not isinstance(p, Port) or type(p.surface) is not int or not 0 <= p.surface < len(bases):
            raise ValueError('invalid port surface')
        if len(p.ends) != 2 or any(type(e) is not int or e < 0 for e in p.ends):
            raise ValueError('invalid port endpoints')
        if type(p.orientation) is not int or p.orientation not in (-1, 1):
            raise ValueError('invalid port orientation')
        if type(p.start) is not int or not 0 <= p.start < core.vertices:
            raise ValueError('invalid port path start')
        v = p.start
        for letter in p.word:
            if type(letter) is not int or letter == 0 or abs(letter) > len(core.edges):
                raise ValueError('invalid port edge')
            a, b = core.edges[abs(letter)-1]
            if letter < 0: a, b = b, a
            if v != a: raise ValueError('noncontiguous port path')
            v = b
        for slot, cv in enumerate((p.start, v)):
            endpoint = p.ends[slot]
            if endpoint in owners and owners[endpoint] != p.surface:
                raise ValueError('endpoint shared by different base components')
            if endpoint in core_vertex and core_vertex[endpoint] != cv:
                raise ValueError('endpoint has inconsistent core image')
            owners[endpoint] = p.surface; core_vertex[endpoint] = cv
            adjacency.setdefault(endpoint, []).append((i, slot))
    if any(len(incidence) not in (1,2) for incidence in adjacency.values()):
        raise ValueError('attachment subset is not a one-manifold')
    circles = [[] for _ in bases]
    intervals = [[] for _ in bases]
    unused = set(range(len(ports)))
    first = 0
    while unused:
        while first not in unused:
            first += 1
        owner = ports[first].surface
        # Find this finite component, using ports rather than base cells.
        comp_edges, comp_vertices = set(), set()
        todo = [ports[first].ends[0]]
        while todo:
            v = todo.pop()
            if v in comp_vertices: continue
            comp_vertices.add(v)
            for i, slot in adjacency[v]:
                comp_edges.add(i)
                todo.append(ports[i].ends[1-slot])
        tips = sorted(v for v in comp_vertices if len(adjacency[v]) == 1)
        if len(tips) not in (0,2):
            raise ValueError('invalid one-manifold component')
        ori = bases[owner].orientable
        if tips:
            start = tips[0]
            i, slot = adjacency[start][0]
            if ori and (1 if slot == 0 else -1) != ports[i].orientation:
                start = tips[1]
        else:
            p = ports[first]
            start = p.ends[0 if not ori or p.orientation == 1 else 1]
        current = start
        walked = set()
        word = []
        while len(walked) < len(comp_edges):
            available = [(i,s) for i,s in adjacency[current] if i not in walked]
            if not available:
                raise ValueError('port walk stopped prematurely')
            if not walked and not tips:
                # For a one-edge circle both endpoint occurrences are present.
                selected = (first, 0 if not ori or ports[first].orientation == 1 else 1)
                if selected not in available: raise ValueError('invalid cycle start')
                i, slot = selected
            else:
                i, slot = available[0]
            p = ports[i]
            direction = 1 if slot == 0 else -1
            if ori and direction != p.orientation:
                raise ValueError('incoherent boundary direction along attachment component')
            word.extend(p.word if slot == 0 else tuple(-x for x in reversed(p.word)))
            walked.add(i)
            current = p.ends[1-slot]
        if tips:
            if current not in tips or current == start:
                raise ValueError('interval did not join its endpoints')
            intervals[owner].append(core_vertex[start])
        else:
            if current != start:
                raise ValueError('circle walk did not close')
            circles[owner].append(Loop(core_vertex[start], tuple(word)))
        unused.difference_update(comp_edges)
    model = Model(core, tuple(replace(s, circles=tuple(circles[i]), intervals=tuple(intervals[i])) for i,s in enumerate(bases)))
    validate(model)
    return model
