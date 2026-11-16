#!/usr/bin/env python3
"""Exact finite kernel for the iPRA topology framework.

The module intentionally uses only finite sets, integers and arithmetic mod 2.
It is an executable reference implementation, not a proof checker for iPRA.

Main objects:
  * finite simplicial complexes;
  * strong simplicial carriers (finite relational maps);
  * carrier composition and deterministic selections;
  * mod-2 chain complexes, Betti numbers, and the prism chain homotopy;
  * finite preorders and their Alexandrov topologies;
  * finite observation towers built from complexes and refinement carriers.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product
import argparse
import json
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, Iterator, List, Mapping, Sequence, Tuple

Simplex = Tuple[int, ...]
BitMatrix = List[List[int]]


def _canonical_simplex(xs: Iterable[int]) -> Simplex:
    values = tuple(sorted(xs))
    if len(values) != len(set(values)):
        raise ValueError("a simplex may not repeat a vertex")
    return values


def _all_nonempty_faces(simplex: Simplex) -> Iterator[Simplex]:
    for r in range(1, len(simplex) + 1):
        yield from combinations(simplex, r)


@dataclass(frozen=True)
class SimplicialComplex:
    """A finite abstract simplicial complex with vertices 0,...,n_vertices-1.

    The empty simplex is implicit. ``simplices`` contains all nonempty faces.
    """

    n_vertices: int
    simplices: FrozenSet[Simplex]

    @staticmethod
    def from_facets(n_vertices: int, facets: Iterable[Iterable[int]]) -> "SimplicialComplex":
        if n_vertices < 0:
            raise ValueError("n_vertices must be nonnegative")
        closure: set[Simplex] = set()
        for raw in facets:
            facet = _canonical_simplex(raw)
            if not facet:
                continue
            if facet[0] < 0 or facet[-1] >= n_vertices:
                raise ValueError("facet vertex outside declared range")
            closure.update(_all_nonempty_faces(facet))
        # Isolated declared vertices are legitimate vertices and hence simplices.
        closure.update((v,) for v in range(n_vertices))
        result = SimplicialComplex(n_vertices, frozenset(closure))
        result.validate()
        return result

    def validate(self) -> None:
        for s in self.simplices:
            if not s:
                raise ValueError("the empty simplex is implicit, not stored")
            if tuple(sorted(s)) != s or len(set(s)) != len(s):
                raise ValueError(f"noncanonical simplex: {s}")
            if s[0] < 0 or s[-1] >= self.n_vertices:
                raise ValueError(f"simplex outside vertex range: {s}")
            for face in _all_nonempty_faces(s):
                if face not in self.simplices:
                    raise ValueError(f"missing face {face} of {s}")
        for v in range(self.n_vertices):
            if (v,) not in self.simplices:
                raise ValueError(f"missing declared vertex {v}")

    @property
    def dimension(self) -> int:
        if not self.simplices:
            return -1
        return max(len(s) - 1 for s in self.simplices)

    def by_dimension(self, q: int) -> Tuple[Simplex, ...]:
        if q < 0:
            return tuple()
        return tuple(sorted(s for s in self.simplices if len(s) == q + 1))

    def contains(self, vertices: Iterable[int]) -> bool:
        values = tuple(sorted(set(vertices)))
        return not values or values in self.simplices


@dataclass(frozen=True)
class Carrier:
    """A strong simplicial carrier from ``source`` to ``target``.

    Each source vertex is assigned a nonempty finite cloud of target vertices.
    For every source simplex sigma, the union of all clouds over sigma must be a
    target simplex. Consequently every point selection is a simplicial map, and
    any two selections are contiguous.
    """

    source: SimplicialComplex
    target: SimplicialComplex
    images: Tuple[FrozenSet[int], ...]

    @staticmethod
    def make(
        source: SimplicialComplex,
        target: SimplicialComplex,
        images: Mapping[int, Iterable[int]] | Sequence[Iterable[int]],
    ) -> "Carrier":
        if isinstance(images, Mapping):
            packed = tuple(frozenset(images[v]) for v in range(source.n_vertices))
        else:
            packed = tuple(frozenset(xs) for xs in images)
        carrier = Carrier(source, target, packed)
        carrier.validate()
        return carrier

    def validate(self) -> None:
        if len(self.images) != self.source.n_vertices:
            raise ValueError("one carrier cloud is required for each source vertex")
        for v, image in enumerate(self.images):
            if not image:
                raise ValueError(f"empty carrier cloud at source vertex {v}")
            if min(image) < 0 or max(image) >= self.target.n_vertices:
                raise ValueError(f"target vertex outside range in cloud at {v}")
        for sigma in self.source.simplices:
            union: set[int] = set()
            for v in sigma:
                union.update(self.images[v])
            if not self.target.contains(union):
                raise ValueError(
                    f"carrier condition fails on source simplex {sigma}: "
                    f"union {tuple(sorted(union))} is not a target simplex"
                )

    @staticmethod
    def identity(complex_: SimplicialComplex) -> "Carrier":
        return Carrier.make(complex_, complex_, [{v} for v in range(complex_.n_vertices)])

    def compose(self, after: "Carrier") -> "Carrier":
        """Return ``after o self``.

        ``self : K -> L`` and ``after : L -> M``. Relational composition is
        finite union: (after o self)(v) = union_{w in self(v)} after(w).
        """
        if self.target != after.source:
            raise ValueError("carrier endpoints do not match for composition")
        composed: List[set[int]] = []
        for cloud in self.images:
            out: set[int] = set()
            for w in cloud:
                out.update(after.images[w])
            composed.append(out)
        return Carrier.make(self.source, after.target, composed)

    def selection(self, mode: str = "min") -> Tuple[int, ...]:
        if mode == "min":
            return tuple(min(xs) for xs in self.images)
        if mode == "max":
            return tuple(max(xs) for xs in self.images)
        raise ValueError("selection mode must be 'min' or 'max'")

    def is_selection(self, selected: Sequence[int]) -> bool:
        return len(selected) == len(self.images) and all(
            selected[v] in self.images[v] for v in range(len(self.images))
        )

    def validate_selection(self, selected: Sequence[int]) -> None:
        if not self.is_selection(selected):
            raise ValueError("the supplied map is not a carrier selection")
        for sigma in self.source.simplices:
            image = {selected[v] for v in sigma}
            if not self.target.contains(image):
                raise ValueError(f"selection is not simplicial on {sigma}")

    def selections_are_contiguous(self, f: Sequence[int], g: Sequence[int]) -> bool:
        self.validate_selection(f)
        self.validate_selection(g)
        return all(
            self.target.contains({f[v] for v in sigma} | {g[v] for v in sigma})
            for sigma in self.source.simplices
        )


def mat_zero(rows: int, cols: int) -> BitMatrix:
    return [[0 for _ in range(cols)] for _ in range(rows)]


def mat_add_mod2(a: BitMatrix, b: BitMatrix) -> BitMatrix:
    if len(a) != len(b) or (a and len(a[0]) != len(b[0])):
        raise ValueError("matrix shapes differ")
    return [[x ^ y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mat_mul_mod2(a: BitMatrix, b: BitMatrix) -> BitMatrix:
    a_rows = len(a)
    a_cols = len(a[0]) if a else 0
    b_rows = len(b)
    b_cols = len(b[0]) if b else 0
    if a_cols != b_rows:
        raise ValueError(f"matrix shapes do not compose: {a_rows}x{a_cols}, {b_rows}x{b_cols}")
    out = mat_zero(a_rows, b_cols)
    for i in range(a_rows):
        for k in range(a_cols):
            if a[i][k]:
                for j in range(b_cols):
                    out[i][j] ^= b[k][j]
    return out


def rank_mod2(matrix: BitMatrix) -> int:
    if not matrix:
        return 0
    a = [row[:] for row in matrix]
    rows = len(a)
    cols = len(a[0])
    if any(len(row) != cols for row in a):
        raise ValueError("ragged matrix")
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        for r in range(rows):
            if r != rank and a[r][col]:
                a[r] = [x ^ y for x, y in zip(a[r], a[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def boundary_matrix(complex_: SimplicialComplex, q: int) -> BitMatrix:
    """Matrix C_q -> C_{q-1} over F_2."""
    cols = complex_.by_dimension(q)
    rows = complex_.by_dimension(q - 1)
    if q <= 0:
        return mat_zero(0, len(cols))
    row_index = {s: i for i, s in enumerate(rows)}
    out = mat_zero(len(rows), len(cols))
    for j, sigma in enumerate(cols):
        for i in range(len(sigma)):
            face = sigma[:i] + sigma[i + 1 :]
            out[row_index[face]][j] ^= 1
    return out


def betti_numbers_mod2(complex_: SimplicialComplex) -> Tuple[int, ...]:
    """Return beta_q = dim H_q(K; F_2) for all dimensions present."""
    if complex_.dimension < 0:
        return tuple()
    counts = [len(complex_.by_dimension(q)) for q in range(complex_.dimension + 1)]
    ranks = [rank_mod2(boundary_matrix(complex_, q)) for q in range(complex_.dimension + 1)]
    # rank of D_{d+1}=0 above top dimension.
    ranks.append(0)
    return tuple(counts[q] - ranks[q] - ranks[q + 1] for q in range(len(counts)))


def _normalized_image(simplex: Simplex, vertex_map: Sequence[int]) -> Simplex | None:
    image = tuple(vertex_map[v] for v in simplex)
    if len(set(image)) != len(image):
        return None
    return tuple(sorted(image))


def chain_map_matrix(
    source: SimplicialComplex,
    target: SimplicialComplex,
    vertex_map: Sequence[int],
    q: int,
) -> BitMatrix:
    if len(vertex_map) != source.n_vertices:
        raise ValueError("vertex map has wrong arity")
    source_q = source.by_dimension(q)
    target_q = target.by_dimension(q)
    row_index = {s: i for i, s in enumerate(target_q)}
    out = mat_zero(len(target_q), len(source_q))
    for j, sigma in enumerate(source_q):
        image = _normalized_image(sigma, vertex_map)
        if image is None:
            continue
        if image not in row_index:
            raise ValueError(f"vertex map is not simplicial on {sigma}; image={image}")
        out[row_index[image]][j] ^= 1
    return out


def prism_matrix_mod2(
    source: SimplicialComplex,
    target: SimplicialComplex,
    f: Sequence[int],
    g: Sequence[int],
    q: int,
) -> BitMatrix:
    """The standard prism P_q : C_q(source) -> C_{q+1}(target) over F_2."""
    source_q = source.by_dimension(q)
    target_next = target.by_dimension(q + 1)
    row_index = {s: i for i, s in enumerate(target_next)}
    out = mat_zero(len(target_next), len(source_q))
    for j, sigma in enumerate(source_q):
        for i in range(q + 1):
            word = tuple(f[sigma[t]] for t in range(i + 1)) + tuple(
                g[sigma[t]] for t in range(i, q + 1)
            )
            if len(set(word)) != len(word):
                continue
            term = tuple(sorted(word))
            if term not in row_index:
                raise ValueError(
                    f"maps are not contiguous on {sigma}; prism term {term} is absent"
                )
            out[row_index[term]][j] ^= 1
    return out


def verify_prism_identity(carrier: Carrier, f: Sequence[int], g: Sequence[int]) -> bool:
    """Check dP + Pd = f_# + g_# in every dimension over F_2."""
    carrier.validate_selection(f)
    carrier.validate_selection(g)
    if not carrier.selections_are_contiguous(f, g):
        return False
    k = carrier.source
    l = carrier.target
    for q in range(k.dimension + 1):
        lq = len(l.by_dimension(q))
        kq = len(k.by_dimension(q))
        lnext = len(l.by_dimension(q + 1))
        d_target = boundary_matrix(l, q + 1)
        p_q = prism_matrix_mod2(k, l, f, g, q)
        # A list-of-lists representation cannot retain the column count of a
        # matrix with zero rows.  In this boundary case the product is the
        # uniquely determined zero matrix of the advertised shape.
        term1 = mat_zero(lq, kq) if lnext == 0 else mat_mul_mod2(d_target, p_q)

        if q == 0:
            term2 = mat_zero(lq, kq)
        else:
            p_prev = prism_matrix_mod2(k, l, f, g, q - 1)
            d_source = boundary_matrix(k, q)
            term2 = mat_zero(lq, kq) if lq == 0 else mat_mul_mod2(p_prev, d_source)

        f_q = chain_map_matrix(k, l, f, q)
        g_q = chain_map_matrix(k, l, g, q)
        lhs = mat_add_mod2(term1, term2)
        rhs = mat_add_mod2(f_q, g_q)
        if lhs != rhs:
            return False
    return True


@dataclass(frozen=True)
class FinitePreorder:
    relation: Tuple[Tuple[bool, ...], ...]

    @staticmethod
    def make(relation: Sequence[Sequence[bool | int]]) -> "FinitePreorder":
        packed = tuple(tuple(bool(x) for x in row) for row in relation)
        result = FinitePreorder(packed)
        result.validate()
        return result

    @property
    def size(self) -> int:
        return len(self.relation)

    def validate(self) -> None:
        n = len(self.relation)
        if any(len(row) != n for row in self.relation):
            raise ValueError("preorder relation must be square")
        for x in range(n):
            if not self.relation[x][x]:
                raise ValueError("preorder is not reflexive")
        for x in range(n):
            for y in range(n):
                if self.relation[x][y]:
                    for z in range(n):
                        if self.relation[y][z] and not self.relation[x][z]:
                            raise ValueError("preorder is not transitive")

    def is_open(self, subset: FrozenSet[int]) -> bool:
        """Upward-open convention: x in U and x <= y imply y in U."""
        return all(
            (not self.relation[x][y]) or (y in subset)
            for x in subset
            for y in range(self.size)
        )

    def opens(self) -> Tuple[FrozenSet[int], ...]:
        result: List[FrozenSet[int]] = []
        for mask in range(1 << self.size):
            subset = frozenset(i for i in range(self.size) if (mask >> i) & 1)
            if self.is_open(subset):
                result.append(subset)
        return tuple(result)

    def monotone_to(self, target: "FinitePreorder", mapping: Sequence[int]) -> bool:
        if len(mapping) != self.size:
            return False
        if any(y < 0 or y >= target.size for y in mapping):
            return False
        return all(
            not self.relation[x][xp] or target.relation[mapping[x]][mapping[xp]]
            for x in range(self.size)
            for xp in range(self.size)
        )

    def continuous_to(self, target: "FinitePreorder", mapping: Sequence[int]) -> bool:
        if len(mapping) != self.size:
            return False
        for open_set in target.opens():
            inverse = frozenset(x for x in range(self.size) if mapping[x] in open_set)
            if not self.is_open(inverse):
                return False
        return True


@dataclass(frozen=True)
class ObservationTower:
    """A finite prefix of an inverse tower of complexes and carrier refinements."""

    levels: Tuple[SimplicialComplex, ...]
    # refinements[k] : levels[k+1] -> levels[k]
    refinements: Tuple[Carrier, ...]

    @staticmethod
    def make(levels: Sequence[SimplicialComplex], refinements: Sequence[Carrier]) -> "ObservationTower":
        tower = ObservationTower(tuple(levels), tuple(refinements))
        tower.validate()
        return tower

    def validate(self) -> None:
        if len(self.refinements) + 1 != len(self.levels):
            raise ValueError("a tower of r levels needs r-1 refinement carriers")
        for k, carrier in enumerate(self.refinements):
            if carrier.source != self.levels[k + 1] or carrier.target != self.levels[k]:
                raise ValueError(f"refinement {k} has wrong endpoints")
            carrier.validate()

    def refinement(self, fine: int, coarse: int) -> Carrier:
        """Composite carrier levels[fine] -> levels[coarse], fine >= coarse."""
        if not (0 <= coarse <= fine < len(self.levels)):
            raise ValueError("invalid level interval")
        result = Carrier.identity(self.levels[fine])
        for k in range(fine - 1, coarse - 1, -1):
            result = result.compose(self.refinements[k])
        return result


def cycle_complex(n: int) -> SimplicialComplex:
    if n < 3:
        raise ValueError("cycle needs at least three vertices")
    edges = [(i, (i + 1) % n) for i in range(n)]
    return SimplicialComplex.from_facets(n, edges)


def cycle_refinement(fine_n: int, coarse_n: int) -> Carrier:
    if fine_n != 2 * coarse_n:
        raise ValueError("this reference refinement expects a binary subdivision")
    source = cycle_complex(fine_n)
    target = cycle_complex(coarse_n)
    images: List[set[int]] = []
    for j in range(fine_n):
        if j % 2 == 0:
            images.append({(j // 2) % coarse_n})
        else:
            images.append({(j // 2) % coarse_n, (j // 2 + 1) % coarse_n})
    return Carrier.make(source, target, images)


def example_report() -> dict:
    c4 = cycle_complex(4)
    c8 = cycle_complex(8)
    c16 = cycle_complex(16)
    r8_4 = cycle_refinement(8, 4)
    r16_8 = cycle_refinement(16, 8)
    tower = ObservationTower.make([c4, c8, c16], [r8_4, r16_8])
    composite = tower.refinement(2, 0)
    f = r8_4.selection("min")
    g = r8_4.selection("max")

    sierpinski = FinitePreorder.make([[1, 1], [0, 1]])
    discrete2 = FinitePreorder.make([[1, 0], [0, 1]])

    return {
        "cycle_betti": {
            "C4": list(betti_numbers_mod2(c4)),
            "C8": list(betti_numbers_mod2(c8)),
            "C16": list(betti_numbers_mod2(c16)),
        },
        "carrier": {
            "min_selection": list(f),
            "max_selection": list(g),
            "contiguous": r8_4.selections_are_contiguous(f, g),
            "prism_identity_mod2": verify_prism_identity(r8_4, f, g),
            "composite_cloud_sizes": [len(x) for x in composite.images],
        },
        "finite_topology": {
            "sierpinski_open_sets": [sorted(x) for x in sierpinski.opens()],
            "discrete_two_point_open_count": len(discrete2.opens()),
            "monotone_continuous_equivalence_checked": all(
                sierpinski.monotone_to(sierpinski, m)
                == sierpinski.continuous_to(sierpinski, m)
                for m in product(range(2), repeat=2)
            ),
        },
    }


def complex_from_json(data: Mapping[str, object]) -> SimplicialComplex:
    return SimplicialComplex.from_facets(
        int(data["n_vertices"]),
        data["facets"],  # type: ignore[arg-type]
    )


def validate_json_certificate(data: Mapping[str, object]) -> dict:
    source = complex_from_json(data["source_complex"])  # type: ignore[arg-type]
    target = complex_from_json(data["target_complex"])  # type: ignore[arg-type]
    images_data = data["carrier_images"]  # type: ignore[assignment]
    images = {int(k): v for k, v in images_data.items()}  # type: ignore[union-attr]
    carrier = Carrier.make(source, target, images)
    f = carrier.selection("min")
    g = carrier.selection("max")
    report = {
        "valid": True,
        "source_betti_mod2": list(betti_numbers_mod2(source)),
        "target_betti_mod2": list(betti_numbers_mod2(target)),
        "min_selection": list(f),
        "max_selection": list(g),
        "contiguous": carrier.selections_are_contiguous(f, g),
        "prism_identity_mod2": verify_prism_identity(carrier, f, g),
    }
    expected = data.get("expected")
    if isinstance(expected, Mapping):
        for key, value in expected.items():
            if report.get(key) != value:
                raise ValueError(f"expected {key}={value!r}, got {report.get(key)!r}")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, help="JSON certificate to validate")
    parser.add_argument("--example", action="store_true", help="print the built-in regression report")
    args = parser.parse_args()
    try:
        if args.certificate is not None:
            data = json.loads(args.certificate.read_text(encoding="utf-8"))
            report = validate_json_certificate(data)
        else:
            report = example_report()
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(json.dumps({"valid": False, "error": str(exc)}, indent=2, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
