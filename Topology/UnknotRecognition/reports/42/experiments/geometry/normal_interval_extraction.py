"""Extract normal-disc and between-disc face identifications in binary size.

Input coordinates use [T0,T1,T2,T3,Q01|23,Q02|13,Q03|12]. A face record is
None or {"tetrahedron": u, "permutation": [p0,p1,p2,p3]}, with a reciprocal
record. The module checks this combinatorial format, normal matching, and
quadrilateral constraints. It assumes the face pairing describes a finite
triangulated 3-manifold; it does not certify manifold links, knot-exterior
provenance, irreducibility, or any recognition verdict.

The output is an exact polygon-gluing presentation of the normal surface,
using stacks and affine maps on intervals. It also records the identifications
between consecutive-disc prism pieces and the bounded local complement cells.
It does NOT compute global parallelity bundles, edge-neighbourhood cleanup,
compressed component orbits, or a complete cut-manifold triangulation.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Callable


class ExtractionError(ValueError):
    """The supplied face pairing or normal vector is not in the input format."""


QUAD_SIDES = ((0, 1), (0, 2), (0, 3))
COORDINATE_ORDER = ("T0", "T1", "T2", "T3", "Q01|23", "Q02|13", "Q03|12")


def _integer(value, name: str, *, hexadecimal: bool = False) -> int:
    if type(value) is int:
        return value
    if hexadecimal and type(value) is str:
        digits = value[2:] if value.startswith("0x") else ""
        if digits and all(character in "0123456789abcdefABCDEF" for character in digits):
            return int(digits, 16)
    raise ExtractionError(f"{name} must be an integer" + (" or nonnegative hexadecimal integer" if hexadecimal else ""))


def encode_large_integers(value, *, threshold_bits: int = 256):
    """Make JSON output independent of Python's decimal digit conversion cap."""
    if type(value) is int and value.bit_length() > threshold_bits:
        return hex(value)
    if type(value) is dict:
        return {key: encode_large_integers(item, threshold_bits=threshold_bits)
                for key, item in value.items()}
    if type(value) in (tuple, list):
        return [encode_large_integers(item, threshold_bits=threshold_bits) for item in value]
    return value


@dataclass(frozen=True)
class DiscStack:
    identifier: int
    tetrahedron: int
    coordinate: int
    count: int
    # Cyclic polygon corners, each labelled by a tetrahedron edge.
    corners: tuple[tuple[int, int], ...]
    # Face containing each cyclic polygon side.
    side_faces: tuple[int, ...]
    # Consecutive discs are numbered from before_cell towards after_cell.
    before_cell: str
    after_cell: str


@dataclass(frozen=True)
class FaceBand:
    """Match j in [start,stop) to sign*j+offset in the target stack."""
    source_stack: int
    target_stack: int
    start: int
    stop: int
    sign: int
    offset: int
    source_face: int
    target_face: int
    source_arc_vertex: int
    target_arc_vertex: int
    permutation: tuple[int, int, int, int]
    # Orientations of glued polygon interiors transport by this multiplier.
    orientation_multiplier: int


@dataclass(frozen=True)
class BoundaryBand:
    stack: int
    face: int
    arc_vertex: int
    count: int


@dataclass(frozen=True)
class PrismFrontierBand:
    """Unglued sides of local gap prisms, with exact endpoint provenance."""
    stack: int
    start: int
    stop: int
    face: int
    kind: str
    target_tetrahedron: int | None
    target_face: int | None
    target_residual_cell: str | None


@dataclass(frozen=True)
class Extraction:
    tetrahedra: int
    stacks: tuple[DiscStack, ...]
    surface_bands: tuple[FaceBand, ...]
    prism_bands: tuple[FaceBand, ...]
    boundary_bands: tuple[BoundaryBand, ...]
    prism_frontier_bands: tuple[PrismFrontierBand, ...]
    # The cells remaining in a tetrahedron after its interdisc prisms are removed.
    local_residual_cells: tuple[tuple[str, ...], ...]
    paired_faces: int
    boundary_faces: int
    input_coordinate_bits: int

    def statistics(self):
        discs = sum(stack.count for stack in self.stacks)
        prisms = sum(stack.count - 1 for stack in self.stacks)
        residue = sum(len(cells) for cells in self.local_residual_cells)
        return {
            "tetrahedra": self.tetrahedra,
            "nonempty_disc_stacks": len(self.stacks),
            "normal_discs": discs,
            "between_disc_prisms": prisms,
            "local_complement_cells": discs + self.tetrahedra,
            "local_residual_cells": residue,
            "surface_face_bands": len(self.surface_bands),
            "prism_face_bands": len(self.prism_bands),
            "boundary_arc_bands": len(self.boundary_bands),
            "prism_frontier_bands": len(self.prism_frontier_bands),
            "prism_to_residual_contacts": sum(band.stop - band.start
                for band in self.prism_frontier_bands if band.kind == "opposite_residual_cell"),
            "paired_faces": self.paired_faces,
            "boundary_faces": self.boundary_faces,
            "coordinate_bits": self.input_coordinate_bits,
        }

    def as_dict(self, *, hexadecimal: bool = True):
        data = asdict(self)
        data["statistics"] = self.statistics()
        data["version"] = 1
        data["coordinate_order"] = COORDINATE_ORDER
        data["scope"] = (
            "exact normal polygon face gluings and local interdisc-prism face data; "
            "no global parallelity-bundle or knot-recognition verdict"
        )
        return encode_large_integers(data) if hexadecimal else data


@dataclass(frozen=True)
class _ArcBlock:
    stack: int
    rank_start: int
    rank_stop: int
    # Face rank = sign * disc_index + offset.
    sign: int
    offset: int


def _prepare(triangulation, coordinates, check):
    check()
    if (type(triangulation) is not dict or set(triangulation) != {"tetrahedra"}
            or type(triangulation["tetrahedra"]) is not list
            or not triangulation["tetrahedra"]):
        raise ExtractionError("expected a nonempty tetrahedra array")
    tetrahedra = triangulation["tetrahedra"]
    size = len(tetrahedra)
    prepared = []
    for tetrahedron, faces in enumerate(tetrahedra):
        check()
        if type(faces) is not list or len(faces) != 4:
            raise ExtractionError("each tetrahedron needs four faces")
        row = []
        for face, record in enumerate(faces):
            if record is None:
                row.append(None)
                continue
            if (type(record) is not dict or set(record) != {"tetrahedron", "permutation"}
                    or type(record["permutation"]) not in (list, tuple)
                    or len(record["permutation"]) != 4):
                raise ExtractionError("invalid face pairing record")
            target = _integer(record["tetrahedron"], "target tetrahedron")
            permutation = tuple(_integer(value, "permutation entry") for value in record["permutation"])
            if not 0 <= target < size or set(permutation) != {0, 1, 2, 3}:
                raise ExtractionError("invalid target tetrahedron or permutation")
            if (target, permutation[face]) == (tetrahedron, face):
                raise ExtractionError("a face cannot be paired with itself")
            row.append((target, permutation))
        prepared.append(tuple(row))
    for tetrahedron, faces in enumerate(prepared):
        check()
        for face, record in enumerate(faces):
            if record is None:
                continue
            target, permutation = record
            inverse = tuple(permutation.index(vertex) for vertex in range(4))
            if prepared[target][permutation[face]] != (tetrahedron, inverse):
                raise ExtractionError("face pairings must be reciprocal")
    if type(coordinates) not in (list, tuple) or len(coordinates) != size:
        raise ExtractionError("one normal coordinate row is required per tetrahedron")
    rows = []
    for row in coordinates:
        check()
        if type(row) not in (tuple, list) or len(row) != 7:
            raise ExtractionError("seven normal coordinates are required per tetrahedron")
        converted = tuple(_integer(value, "normal coordinate", hexadecimal=True) for value in row)
        if any(value < 0 for value in converted):
            raise ExtractionError("normal coordinates must be nonnegative")
        if sum(value != 0 for value in converted[4:]) > 1:
            raise ExtractionError("quadrilateral constraints fail")
        rows.append(converted)
    return tuple(prepared), tuple(rows)


def polygon_template(coordinate: int):
    """Return oriented corner-edge and side-face labels for one normal disc."""
    if coordinate < 4:
        corners = tuple(tuple(sorted((coordinate, vertex)))
                        for vertex in range(4) if vertex != coordinate)
    else:
        a, b = QUAD_SIDES[coordinate - 4]
        c, d = tuple(vertex for vertex in range(4) if vertex not in (a, b))
        corners = tuple(tuple(sorted(edge)) for edge in ((a, c), (a, d), (b, d), (b, c)))
    side_faces = tuple(next(iter({0, 1, 2, 3} - set(corners[index])
                                - set(corners[(index + 1) % len(corners)])))
                       for index in range(len(corners)))
    return corners, side_faces


def _quad_arc_vertex(coordinate: int, face: int) -> int:
    side = QUAD_SIDES[coordinate - 4]
    same_side = side if face in side else tuple(vertex for vertex in range(4) if vertex not in side)
    return next(vertex for vertex in same_side if vertex != face)


def _orientation_multiplier(source: DiscStack, target: DiscStack,
                            source_face: int, target_face: int, permutation) -> int:
    left = source.side_faces.index(source_face)
    right = target.side_faces.index(target_face)
    mapped_first = tuple(sorted(permutation[vertex] for vertex in source.corners[left]))
    mapped_second = tuple(sorted(permutation[vertex]
                                 for vertex in source.corners[(left + 1) % len(source.corners)]))
    target_first = target.corners[right]
    target_second = target.corners[(right + 1) % len(target.corners)]
    if (mapped_first, mapped_second) == (target_first, target_second):
        return -1
    if (mapped_first, mapped_second) == (target_second, target_first):
        return 1
    raise ExtractionError("normal polygon endpoints do not match the face permutation")


def extract_normal_intervals(triangulation, coordinates, *,
                             check: Callable[[], None] = lambda: None) -> Extraction:
    """Extract O(t) interval records, independently of the numerical disc count.

    Cancellation propagates. All interval endpoints are half-open. For a prism
    band, j numbers the gap between discs j and j+1; its sign is also the fibre
    orientation multiplier. The surface orientation multiplier has no claimed
    interpretation as the orientation character of a globally assembled bundle.
    """
    faces, coordinates = _prepare(triangulation, coordinates, check)
    stacks = []
    stack_index = [[None] * 7 for _ in faces]
    local_cells = []
    active_quads = []
    for tetrahedron, row in enumerate(coordinates):
        check()
        quad = next((coordinate for coordinate in range(4, 7) if row[coordinate]), None)
        active_quads.append(quad)
        cells = ["core"] if quad is None else ["core_A", "core_B"]
        cells.extend(f"vertex_{vertex}" for vertex in range(4) if row[vertex])
        local_cells.append(tuple(cells))
        for coordinate, count in enumerate(row):
            if not count:
                continue
            corners, side_faces = polygon_template(coordinate)
            if coordinate < 4:
                before = f"vertex_{coordinate}"
                after = ("core" if quad is None else
                         "core_A" if coordinate in QUAD_SIDES[quad - 4] else "core_B")
            else:
                before, after = "core_A", "core_B"
            identifier = len(stacks)
            stack_index[tetrahedron][coordinate] = identifier
            stacks.append(DiscStack(identifier, tetrahedron, coordinate, count,
                                    corners, side_faces, before, after))

    def blocks(tetrahedron, face, vertex):
        row = coordinates[tetrahedron]
        triangle_count = row[vertex]
        result = []
        if triangle_count:
            result.append(_ArcBlock(stack_index[tetrahedron][vertex], 0,
                                    triangle_count, 1, 0))
        quad = active_quads[tetrahedron]
        if quad is not None and _quad_arc_vertex(quad, face) == vertex:
            count = row[quad]
            sign = 1 if face in QUAD_SIDES[quad - 4] else -1
            offset = triangle_count + (count - 1 if sign == -1 else 0)
            result.append(_ArcBlock(stack_index[tetrahedron][quad], triangle_count,
                                    triangle_count + count, sign, offset))
        return result

    surface_bands = []
    prism_bands = []
    boundary_bands = []
    prism_frontier_bands = []
    paired_faces = 0
    boundary_faces = 0

    def add_internal_frontier(source, target, source_face, target_tetrahedron,
                              target_face, target_vertex):
        # A target face has at most one triangle/quad transition. If it lies
        # inside a source block, one source prism side abuts a residual cell.
        if len(target) != 2:
            return
        rank = target[0].rank_stop
        for block in source:
            if block.rank_start < rank < block.rank_stop:
                first = block.sign * (rank - 1 - block.offset)
                second = block.sign * (rank - block.offset)
                gap = min(first, second)
                quad = active_quads[target_tetrahedron]
                cell = "core_A" if target_vertex in QUAD_SIDES[quad - 4] else "core_B"
                prism_frontier_bands.append(PrismFrontierBand(block.stack, gap, gap + 1,
                    source_face, "opposite_residual_cell", target_tetrahedron, target_face, cell))

    for tetrahedron, row in enumerate(faces):
        check()
        for face, record in enumerate(row):
            if record is None:
                boundary_faces += 1
                for vertex in range(4):
                    if vertex != face:
                        for block in blocks(tetrahedron, face, vertex):
                            boundary_bands.append(BoundaryBand(block.stack, face, vertex,
                                                               block.rank_stop - block.rank_start))
                            count = stacks[block.stack].count
                            if count >= 2:
                                prism_frontier_bands.append(PrismFrontierBand(block.stack,
                                    0, count - 1, face, "ambient_boundary", None, None, None))
                continue
            target_tetrahedron, permutation = record
            target_face = permutation[face]
            if (tetrahedron, face) > (target_tetrahedron, target_face):
                continue
            paired_faces += 1
            face_band_start = len(surface_bands)
            for vertex in range(4):
                if vertex == face:
                    continue
                left = blocks(tetrahedron, face, vertex)
                right = blocks(target_tetrahedron, target_face, permutation[vertex])
                left_total = left[-1].rank_stop if left else 0
                right_total = right[-1].rank_stop if right else 0
                if left_total != right_total:
                    raise ExtractionError("normal matching equations fail")
                add_internal_frontier(left, right, face, target_tetrahedron,
                                      target_face, permutation[vertex])
                add_internal_frontier(right, left, target_face, tetrahedron, face, vertex)
                for source_block in left:
                    for target_block in right:
                        rank_start = max(source_block.rank_start, target_block.rank_start)
                        rank_stop = min(source_block.rank_stop, target_block.rank_stop)
                        if rank_start >= rank_stop:
                            continue
                        first = source_block.sign * (rank_start - source_block.offset)
                        last = source_block.sign * (rank_stop - 1 - source_block.offset)
                        start, stop = min(first, last), max(first, last) + 1
                        sign = target_block.sign * source_block.sign
                        offset = target_block.sign * (source_block.offset - target_block.offset)
                        orientation = _orientation_multiplier(stacks[source_block.stack],
                            stacks[target_block.stack], face, target_face, permutation)
                        band = FaceBand(source_block.stack, target_block.stack, start, stop,
                                        sign, offset, face, target_face, vertex,
                                        permutation[vertex], permutation, orientation)
                        surface_bands.append(band)
                        if stop - start >= 2:
                            # For a reflected pair, the target lower disc is f(j+1).
                            prism_bands.append(FaceBand(source_block.stack, target_block.stack,
                                start, stop - 1, sign, offset - int(sign == -1), face,
                                target_face, vertex, permutation[vertex], permutation, orientation))
            if len(surface_bands) - face_band_start > 5:
                raise RuntimeError("internal error: face-band bound violated")
    result = Extraction(len(faces), tuple(stacks), tuple(surface_bands), tuple(prism_bands),
                        tuple(boundary_bands), tuple(prism_frontier_bands), tuple(local_cells),
                        paired_faces, boundary_faces,
                        sum(max(1, value.bit_length()) for row in coordinates for value in row))
    if result.statistics()["local_residual_cells"] > 6 * len(faces):
        raise RuntimeError("internal error: residual-cell bound violated")
    return result


def orbit_input(result: Extraction, *, orientation_cover: bool = False,
                check: Callable[[], None] = lambda: None):
    """Translate surface bands to one interval; this does not run orbit counting.

    Orbits on the disc interval are the surface's connected components. With
    orientation_cover=True, two labelled copies encode its orientation double
    cover. The target format uses half-open domains and maps z -> sign*z+offset.
    """
    check()
    if type(orientation_cover) is not bool:
        raise ValueError("orientation_cover must be Boolean")
    offsets = []
    total = 0
    for stack in result.stacks:
        check()
        offsets.append(total)
        total += stack.count
    pairings = []
    for band in result.surface_bands:
        check()
        for sheet in range(2 if orientation_cover else 1):
            target_sheet = (sheet ^ int(band.orientation_multiplier == -1)) if orientation_cover else 0
            source_offset = offsets[band.source_stack] + sheet * total
            target_offset = offsets[band.target_stack] + target_sheet * total
            pairings.append({"start": source_offset + band.start,
                             "stop": source_offset + band.stop,
                             "sign": band.sign,
                             "offset": target_offset + band.offset - band.sign * source_offset})
    return {"universe_start": 0, "universe_stop": total * (2 if orientation_cover else 1),
            "pairings": pairings, "orientation_cover": orientation_cover,
            "scope": "input for interval orbit counting; no orbit computation performed"}


def main():
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON with triangulation and coordinates")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--orbit-input", choices=("surface", "orientation"),
                        help="emit the concatenated interval orbit-counter input")
    options = parser.parse_args()
    raw = json.loads(options.input.read_text())
    if type(raw) is not dict or set(raw) != {"triangulation", "coordinates"}:
        raise ExtractionError("input needs exactly triangulation and coordinates")
    result = extract_normal_intervals(raw["triangulation"], raw["coordinates"])
    data = (encode_large_integers(orbit_input(result,
              orientation_cover=options.orbit_input == "orientation"))
            if options.orbit_input else result.as_dict())
    serialized = json.dumps(data, indent=2) + "\n"
    if options.output is None:
        print(serialized, end="")
    else:
        options.output.write_text(serialized)


if __name__ == "__main__":
    main()
