"""Bounded explicit audit tools; these deliberately expand small surfaces.

The Fraction-based face oracle orders geometric normal slices independently
of the extractor's block intersection and affine-coordinate calculations.
Never use these routines to claim binary-size component classification.
"""

from collections import defaultdict, deque
from fractions import Fraction


class _DSU:
    def __init__(self, size):
        self.parent = list(range(size))
        self.size = [1] * size

    def find(self, item):
        while self.parent[item] != item:
            self.parent[item] = self.parent[self.parent[item]]
            item = self.parent[item]
        return item

    def join(self, left, right):
        left, right = self.find(left), self.find(right)
        if left == right:
            return
        if self.size[left] < self.size[right]:
            left, right = right, left
        self.parent[right] = left
        self.size[left] += self.size[right]


def _ensure_small(result, limit):
    if result.statistics()["normal_discs"] > limit:
        raise ValueError("explicit oracle disc limit exceeded")


def geometric_face_map(triangulation, coordinates, result, *, limit=20000):
    """Build each normal slice explicitly and sort its distance from face vertices.

    Triangles use x_v=1-(j+1)/(4(n+1)). A quadrilateral with distinguished
    side A={0,q+1} uses sum_{v in A}x_v=2/3-(j+1)/(3(n+1)). They are disjoint
    slices. Their face positions may be isotoped to match across a face, and
    their vertex-relative order determines the normal gluing uniquely.
    """
    _ensure_small(result, limit)
    stack_ids = {(stack.tetrahedron, stack.coordinate): stack.identifier for stack in result.stacks}
    arcs = defaultdict(list)
    for tetrahedron, row in enumerate(coordinates):
        for coordinate, count in enumerate(row):
            for index in range(count):
                for face in range(4):
                    if coordinate < 4:
                        if face == coordinate:
                            continue
                        vertex = coordinate
                        distance = Fraction(index + 1, 4 * (count + 1))
                    else:
                        side = {0, coordinate - 3}
                        other = {0, 1, 2, 3} - side
                        level = Fraction(2, 3) - Fraction(index + 1, 3 * (count + 1))
                        if face in side:
                            vertex = next(iter(side - {face}))
                            distance = 1 - level
                        else:
                            vertex = next(iter(other - {face}))
                            distance = level
                    arcs[tetrahedron, face, vertex].append((distance, stack_ids[tetrahedron, coordinate], index))
    for key, values in arcs.items():
        values.sort()
        if len({value[0] for value in values}) != len(values):
            raise AssertionError(f"geometric reference has coincident slices at {key}")
    answer = {}
    for tetrahedron, faces in enumerate(triangulation["tetrahedra"]):
        for face, record in enumerate(faces):
            if record is None:
                continue
            target, permutation = record["tetrahedron"], record["permutation"]
            target_face = permutation[face]
            if (tetrahedron, face) > (target, target_face):
                continue
            for vertex in range(4):
                if vertex == face:
                    continue
                left = arcs[tetrahedron, face, vertex]
                right = arcs[target, target_face, permutation[vertex]]
                if len(left) != len(right):
                    raise AssertionError("geometric matching condition fails")
                for (_, source_stack, source_index), (_, target_stack, target_index) in zip(left, right):
                    answer[source_stack, source_index, face] = target_stack, target_index, target_face
    return answer


def expand_bands(bands, *, limit=100000):
    if sum(band.stop - band.start for band in bands) > limit:
        raise ValueError("explicit band limit exceeded")
    answer = {}
    for band in bands:
        for index in range(band.start, band.stop):
            key = band.source_stack, index, band.source_face
            if key in answer:
                raise AssertionError("overlapping source bands")
            answer[key] = (band.target_stack, band.sign * index + band.offset, band.target_face)
    return answer


def check_geometric_pairings(triangulation, coordinates, result):
    reference = geometric_face_map(triangulation, coordinates, result)
    if expand_bands(result.surface_bands) != reference:
        raise AssertionError("compressed surface gluing disagrees with geometric slice oracle")
    expected_prisms = {}
    for (stack, index, face), target in reference.items():
        next_target = reference.get((stack, index + 1, face))
        if next_target is not None and next_target[0] == target[0] and abs(next_target[1] - target[1]) == 1:
            expected_prisms[stack, index, face] = target[0], min(target[1], next_target[1]), target[2]
    if expand_bands(result.prism_bands) != expected_prisms:
        raise AssertionError("compressed prism gluing disagrees with consecutive geometric slices")
    return len(reference), len(expected_prisms)


def expanded_components(result, *, limit=20000):
    """Return exact component coordinates/topology for small extracted surfaces."""
    _ensure_small(result, limit)
    disc_id = {}
    polygon_offsets = []
    polygons = []
    disc_stack = []
    total_corners = 0
    for stack in result.stacks:
        for index in range(stack.count):
            identifier = len(polygons)
            disc_id[stack.identifier, index] = identifier
            polygons.append(stack)
            disc_stack.append(stack)
            polygon_offsets.append(total_corners)
            total_corners += len(stack.corners)
    corners = _DSU(total_corners)
    edges = _DSU(total_corners)
    components = _DSU(len(polygons))
    orientation_graph = [[] for _ in polygons]
    for band in result.surface_bands:
        source, target = result.stacks[band.source_stack], result.stacks[band.target_stack]
        source_side = source.side_faces.index(band.source_face)
        target_side = target.side_faces.index(band.target_face)
        endpoint_map = []
        for corner in (source_side, (source_side + 1) % len(source.corners)):
            mapped = tuple(sorted(band.permutation[vertex] for vertex in source.corners[corner]))
            endpoint_map.append((corner, target.corners.index(mapped)))
        for index in range(band.start, band.stop):
            source_disc = disc_id[band.source_stack, index]
            target_disc = disc_id[band.target_stack, band.sign * index + band.offset]
            source_offset, target_offset = polygon_offsets[source_disc], polygon_offsets[target_disc]
            components.join(source_disc, target_disc)
            edges.join(source_offset + source_side, target_offset + target_side)
            for left, right in endpoint_map:
                corners.join(source_offset + left, target_offset + right)
            orientation_graph[source_disc].append((target_disc, band.orientation_multiplier))
            orientation_graph[target_disc].append((source_disc, band.orientation_multiplier))
    oriented = {}
    nonorientable = set()
    for disc in range(len(polygons)):
        if disc in oriented:
            continue
        oriented[disc] = 1
        pending = [disc]
        while pending:
            current = pending.pop()
            for target, multiplier in orientation_graph[current]:
                sign = oriented[current] * multiplier
                if target in oriented:
                    if oriented[target] != sign:
                        nonorientable.add(components.find(disc))
                else:
                    oriented[target] = sign
                    pending.append(target)
    data = {}
    for identifier, stack in enumerate(polygons):
        root = components.find(identifier)
        item = data.setdefault(root, {"discs": 0, "vertices": set(), "edges": set(),
                                    "boundary_edges": [], "coordinates": [0] * (7 * result.tetrahedra)})
        item["discs"] += 1
        item["coordinates"][7 * stack.tetrahedron + stack.coordinate] += 1
        for corner in range(len(stack.corners)):
            item["vertices"].add(corners.find(polygon_offsets[identifier] + corner))
            item["edges"].add(edges.find(polygon_offsets[identifier] + corner))
    for band in result.boundary_bands:
        stack = result.stacks[band.stack]
        side = stack.side_faces.index(band.face)
        for index in range(band.count):
            disc = disc_id[band.stack, index]
            offset = polygon_offsets[disc]
            a = corners.find(offset + side)
            b = corners.find(offset + (side + 1) % len(stack.corners))
            data[components.find(disc)]["boundary_edges"].append((a, b))
    output = []
    for root, item in data.items():
        graph = defaultdict(list)
        for a, b in item["boundary_edges"]:
            graph[a].append(b)
            graph[b].append(a)
        if any(len(neighbours) != 2 for neighbours in graph.values()):
            raise AssertionError("expanded surface boundary is not a 1-manifold")
        seen = set()
        boundaries = 0
        for vertex in graph:
            if vertex in seen:
                continue
            boundaries += 1
            pending = [vertex]
            seen.add(vertex)
            while pending:
                for other in graph[pending.pop()]:
                    if other not in seen:
                        pending.append(other)
                        seen.add(other)
        output.append({"coordinates": item["coordinates"],
                       "euler": len(item["vertices"]) - len(item["edges"]) + item["discs"],
                       "orientable": root not in nonorientable,
                       "boundaries": boundaries, "discs": item["discs"]})
    return sorted(output, key=lambda item: tuple(item["coordinates"]))


def expanded_interval_orbits(data, *, limit=40000):
    """Small finite equivalence-relation oracle for the single-interval adapter."""
    size = data["universe_stop"]
    if data["universe_start"] != 0 or size > limit:
        raise ValueError("explicit interval orbit limit exceeded")
    relation = _DSU(size)
    for pairing in data["pairings"]:
        for source in range(pairing["start"], pairing["stop"]):
            target = pairing["sign"] * source + pairing["offset"]
            if not 0 <= source < size or not 0 <= target < size:
                raise AssertionError("interval pairing escapes universe")
            relation.join(source, target)
    return len({relation.find(element) for element in range(size)})
