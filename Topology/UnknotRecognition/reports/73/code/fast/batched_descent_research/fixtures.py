"""Deterministic fixed-site batch workloads and a sequential witness oracle."""
from copy import deepcopy
import hashlib
import json

from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from normal_orbit_research.fixtures import layered_torus


def encoded_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return hashlib.sha256(encoded_bytes(value)).hexdigest()


def disjoint_dual_edges(raw):
    """Canonical greedy matching of original tetrahedra across paired faces."""
    pairs, used = [], set()
    for t, row in enumerate(raw['tetrahedra']):
        for f, entry in enumerate(row):
            if entry is None:
                continue
            u = entry['tetrahedron']
            if t != u and t not in used and u not in used:
                pairs.append((t, f, u))
                used.update((t, u))
                break
    return pairs


def source_fixture(kind, count):
    """Build the smallest deterministic selected family large enough here.

    Knot families use adjacent inverse braid letters to enlarge the input
    diagram while preserving its braid element.  The source-to-exterior
    correspondence is independently checked before subsequent expansions.
    """
    if kind == 'layered':
        raw, _ = layered_torus(2 * count)
        source = dict(kind='layered_solid_torus', tetrahedra=2 * count,
                      diagram_bound=False)
    else:
        bases = {'unknot': (2, [1]), 'trefoil': (2, [1, 1, 1]),
                 'figure_eight': (3, [1, -2, 1, -2])}
        if kind not in bases:
            raise ValueError('unknown fixture family')
        strands, base = bases[kind]
        padding = max(0, (count + 7) // 8 - len(base)) // 2
        while True:
            word = base + [1, -1] * padding
            diagram = Diagram.from_braid(strands, word)
            raw = diagram_exterior(diagram)
            if len(disjoint_dual_edges(raw)) >= count:
                break
            padding += 1
        if not verify_diagram_exterior(diagram, raw):
            raise ArithmeticError('source exterior failed its independent checker')
        source = dict(kind=kind, diagram_bound=True, strands=strands,
                      braid_word=word, pd=[list(row) for row in diagram.pd],
                      crossings=diagram.crossings, exterior_verified=True)
    source['initial_tetrahedra'] = len(raw['tetrahedra'])
    source['initial_triangulation_sha256'] = digest(raw)
    heights = rank_one_cocycle_seed(raw)['heights']
    return raw, heights, source


def inflate_disjoint(raw, heights, count):
    """Use checked 2--3 moves on disjoint old pairs, retaining source evidence."""
    pairs = disjoint_dual_edges(raw)[:count]
    if len(pairs) != count:
        raise ValueError('fixture does not have enough disjoint old pairs')
    tags = [('old', i) for i in range(len(raw['tetrahedra']))]
    current, h, expansion = raw, heights, []
    for i, (old_t, f, old_u) in enumerate(pairs):
        t, u = tags.index(('old', old_t)), tags.index(('old', old_u))
        move = pachner_23(current, t, f)
        transport = transport_cocycle(current, h, move['triangulation'], move['certificate'])
        expansion.append(dict(move=deepcopy(move['certificate']),
                              bipyramid_heights=transport['certificate']['bipyramid_heights']))
        tags = [tag for j, tag in enumerate(tags) if j not in (t, u)]
        tags.extend(('up', i, j) for j in range(3))
        current, h = move['triangulation'], transport['heights']
    sites = [dict(tetrahedron=tags.index(('up', i, 0)), vertices=[0, 1])
             for i in range(count)]
    return current, h, sites, expansion


def permuted_output(raw, heights, permutation):
    """Return rows in new-index order; local tetrahedron corners stay fixed."""
    lookup = {old: new for new, old in enumerate(permutation)}
    rows = [[None if entry is None else dict(
        tetrahedron=lookup[entry['tetrahedron']], permutation=list(entry['permutation']))
        for entry in raw['tetrahedra'][old]] for old in permutation]
    return dict(triangulation=dict(tetrahedra=rows),
                heights=[list(heights[old]) for old in permutation])


def sequential_batch(raw, heights, regions, *, check=lambda: None):
    """The old checked one-move APIs, with the same fixed original regions."""
    regions = [{item['tetrahedron']: item['vertices'] for item in entries}
               for entries in regions]
    current, h, moves = raw, heights, []
    tags = [('old', i) for i in range(len(raw['tetrahedra']))]
    for i, region in enumerate(regions):
        check()
        old_t = min(region)
        site = tags.index(('old', old_t))
        vertices = [region[old_t].index(3), region[old_t].index(4)]
        move = pachner_32(current, site, vertices, check=check)
        transport = transport_cocycle(current, h, move['triangulation'],
                                      move['certificate'], check=check)
        moves.append(dict(triangulation=move['triangulation'],
                          transport=transport['certificate']))
        tags = [tag for tag in tags if not (tag[0] == 'old' and tag[1] in region)]
        tags.extend(('new', i, j) for j in range(2))
        current, h = move['triangulation'], transport['heights']
    removed = {t for region in regions for t in region}
    desired = [('old', i) for i in range(len(raw['tetrahedra'])) if i not in removed]
    desired.extend(('new', i, j) for i in range(len(regions)) for j in range(2))
    lookup = {tag: i for i, tag in enumerate(tags)}
    permutation = [lookup[tag] for tag in desired]
    answer = permuted_output(current, h, permutation)
    answer['certificate'] = dict(schema='sequential-cocycle-transport-transcript-v1',
                               moves=moves, canonical_final_permutation=permutation)
    return answer


def verify_sequential_batch(raw, heights, certificate, *, check=lambda: None):
    """Replay the old one-step consumers, without calling their producers."""
    if (type(certificate) is not dict
            or set(certificate) != {'schema', 'moves', 'canonical_final_permutation'}
            or certificate['schema'] != 'sequential-cocycle-transport-transcript-v1'
            or type(certificate['moves']) is not list):
        return False
    current, h = raw, heights
    for move in certificate['moves']:
        check()
        if (type(move) is not dict or set(move) != {'triangulation', 'transport'}
                or not verify_cocycle_transport(current, h, move['triangulation'],
                                                move['transport'], check=check)):
            return False
        current, h = move['triangulation'], move['transport']['heights']
    permutation = certificate['canonical_final_permutation']
    if (type(permutation) is not list
            or any(type(i) is not int for i in permutation)
            or sorted(permutation) != list(range(len(current['tetrahedra'])))):
        return False
    return True
