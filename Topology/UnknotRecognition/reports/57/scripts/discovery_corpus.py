#!/usr/bin/env python3
"""Regina 7.4 fixture corpus for support-restricted normal-disc discovery.

The expected answers come from Regina's full standard-coordinate vertex
enumeration.  This script neither imports nor mutates the upstream package.
Timings below concern vertex enumeration, not knot recognition.  They are
descriptive controls, not evidence of an asymptotic improvement.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
import time

import regina


SEED = 2026100902


def integer(value):
    return int(str(value))


def rows(surface):
    return [[integer(surface.triangles(t, v)) for v in range(4)]
            + [integer(surface.quads(t, q)) for q in range(3)]
            for t in range(surface.triangulation().size())]


def export(triangulation):
    return {"tetrahedra": [[None if tet.adjacentTetrahedron(f) is None else {
        "tetrahedron": tet.adjacentTetrahedron(f).index(),
        "permutation": [tet.adjacentGluing(f)[v] for v in range(4)]}
        for f in range(4)] for tet in triangulation.tetrahedra()]}


def matrix_rank(matrix):
    """Exact fraction-free row reduction, with content removed after each step."""
    a = [list(row) for row in matrix]
    if not a:
        return 0
    pivot_row = 0
    for col in range(len(a[0])):
        other = next((i for i in range(pivot_row,len(a)) if a[i][col]),None)
        if other is None:
            continue
        a[pivot_row],a[other] = a[other],a[pivot_row]
        pivot = a[pivot_row][col]
        for i in range(pivot_row+1,len(a)):
            x = a[i][col]
            if not x:
                continue
            a[i] = [pivot*y-x*z for y,z in zip(a[i],a[pivot_row])]
            content = math.gcd(*a[i])
            if content:
                a[i] = [y//content for y in a[i]]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def sector_metadata(qmatrix,data):
    support = [3*t+q for t,row in enumerate(data)
               for q in range(3) if row[4+q]]
    full_types = [next((q for q in range(3) if row[4+q]),0) for row in data]
    full_columns = [3*t+q for t,q in enumerate(full_types)]
    return {
        "occupied_quad_columns":support,
        "occupied_sector_kernel_dimension":len(support)-matrix_rank(
            [[row[c] for c in support] for row in qmatrix]),
        "full_sector_quad_types":full_types,
        "full_sector_kernel_dimension":len(full_columns)-matrix_rank(
            [[row[c] for c in full_columns] for row in qmatrix]),
    }


def boundary_cap(triangulation):
    result = regina.Triangulation3(triangulation)
    t, f = next((tet.index(), f) for tet in result.tetrahedra()
                for f in range(4) if tet.adjacentTetrahedron(f) is None)
    permutation = [0] * 4
    permutation[f] = 3
    for image, vertex in enumerate(v for v in range(4) if v != f):
        permutation[vertex] = image
    new = result.newTetrahedron()
    result.tetrahedron(t).join(f, new, regina.Perm4(*permutation))
    return result


def pachner_23(triangulation, count, seed):
    result = regina.Triangulation3(triangulation)
    rng = random.Random(seed)
    trace = []
    for _ in range(count):
        order = list(range(result.countTriangles()))
        rng.shuffle(order)
        for i in order:
            if result.pachner(result.triangle(i)):
                trace.append(i)
                break
        else:
            raise RuntimeError("No legal 2-3 Pachner move")
    return result, trace


def fixtures():
    out = []
    a, b = 1, 2
    for n in range(1, 11):
        out.append((f"fibonacci_lst_{n:02}", regina.Example3.lst(a, b), {
            "type": "solid_torus", "construction": "Example3.lst",
            "parameters": [a, b], "family": "Fibonacci layered tori"}))
        a, b = b, a+b
    for a, b in [(0,1),(1,1),(1,3),(1,5),(1,8),(2,5),(2,7),(3,7),
                 (3,8),(4,7),(4,9),(5,7),(5,12),(7,10)]:
        out.append((f"lst_{a}_{b}", regina.Example3.lst(a,b), {
            "type": "solid_torus", "construction": "Example3.lst",
            "parameters": [a,b], "family": "other layered tori"}))
    for base in [(1,2),(3,5)]:
        t = regina.Example3.lst(*base)
        for c in range(1,4):
            t = boundary_cap(t)
            out.append((f"cap_{base[0]}_{base[1]}_{c}",
                        regina.Triangulation3(t), {
                "type": "solid_torus", "construction": "boundary_caps",
                "parameters": list(base), "caps": c,
                "family": "multiple boundary vertices"}))
    for base in [(1,2),(2,3),(3,5)]:
        t = regina.Example3.lst(*base)
        assert t.pachner(t.tetrahedron(0))
        out.append((f"interior_{base[0]}_{base[1]}", t, {
            "type": "solid_torus", "construction": "1-4 Pachner on tet 0",
            "parameters": list(base), "family": "interior vertices"}))
    for base in [(2,3),(3,5),(5,8)]:
        for c in [1,2,3]:
            seed = SEED + 100*base[0] + c
            t, trace = pachner_23(regina.Example3.lst(*base), c, seed)
            out.append((f"pachner23_{base[0]}_{base[1]}_{c}", t, {
                "type": "solid_torus", "construction": "2-3 Pachner moves",
                "parameters": list(base), "moves": trace, "seed": seed,
                "family": "nonlayered solid tori"}))
    for name in ["trefoil", "figureEight"]:
        t = getattr(regina.Example3,name)()
        ideal_isosig = t.isoSig()
        assert t.idealToFinite()
        t.simplify()
        out.append((f"finite_{name}", t, {
            "type": "nontrivial_knot_exterior",
            "construction": "idealToFinite then simplify",
            "parameters": [name], "ideal_isosig": ideal_isosig,
            "family": "finite knot exteriors"}))
        interior = regina.Triangulation3(t)
        assert interior.pachner(interior.tetrahedron(0))
        out.append((f"finite_{name}_interior", interior, {
            "type": "nontrivial_knot_exterior",
            "construction": "finite example then 1-4 Pachner on tet 0",
            "parameters": [name], "ideal_isosig": ideal_isosig,
            "family": "interior vertices in knot exteriors"}))
    for name,closed in [("rp3",regina.Example3.lens(2,1)),
                        ("s2xs1",regina.Example3.s2xs1())]:
        t = regina.Example3.lst(1,2)
        t.connectedSumWith(closed)
        t.simplify()
        out.append((f"solid_torus_sum_{name}",t,{
            "type":"reducible_torus_boundary","has_essential_disc":True,
            "construction":"lst(1,2) connected sum, then simplify",
            "parameters":[name],"family":"positive Euler counterexamples"}))
    return out


def support_histogram(surfaces):
    return dict(sorted(Counter(
        sum(integer(s.quads(t,q)) != 0 for t in range(s.triangulation().size())
            for q in range(3)) for s in surfaces).items()))


def surface_record(surface,qmatrix):
    data = rows(surface)
    flat = [x for row in data for x in row]
    chi = integer(surface.eulerChar())
    compact = surface.isCompact()
    embedded = surface.embedded()
    # All inputs here are compact triangulations, and every enumerated ray is
    # primitive and embedded.  Regina guarantees that vertex surfaces are
    # connected; its API explicitly permits knownConnected=True in this case.
    essential_disc = (chi == 1 and surface.isCompressingDisc(True))
    return {
        "coordinates": data,
        "euler_characteristic": chi,
        "quadrilateral_support": sum(x != 0 for row in data for x in row[4:]),
        "normal_discs": sum(flat),
        "maximum_coordinate": max(flat,default=0),
        "maximum_coordinate_bits": max(flat,default=0).bit_length(),
        "compact": compact,
        "embedded": embedded,
        "has_real_boundary": surface.hasRealBoundary(),
        "orientable":surface.isOrientable(),
        "two_sided":surface.isTwoSided(),
        "boundary_components":surface.countBoundaries(),
        "essential_disc": essential_disc,
        **sector_metadata(qmatrix,data),
    }


def vector_set(surfaces):
    return {tuple(x for row in rows(s) for x in row) for s in surfaces}


def benchmark_enumeration(triangulation, repeats, rng):
    which = regina.NormalList.Vertex | regina.NormalList.EmbeddedOnly
    arms = {
        "regina_default": regina.NormalAlg.Default,
        "regina_standard_direct_dd": (
            regina.NormalAlg.VertexStandardDirect | regina.NormalAlg.VertexDD),
        "regina_via_reduced_tree": (
            regina.NormalAlg.VertexViaReduced | regina.NormalAlg.VertexTree),
    }
    warmups, actual, vectors = {}, {}, {}
    for name, alg in arms.items():
        start = time.perf_counter()
        ss = regina.NormalSurfaces(triangulation,regina.NormalCoords.Standard,
                                   which,alg)
        warmups[name] = time.perf_counter()-start
        actual[name] = str(ss.algorithm())
        vectors[name] = vector_set(ss)
    assert all(v == vectors["regina_default"] for v in vectors.values())
    samples = []
    for repeat in range(repeats):
        order = list(arms)
        rng.shuffle(order)
        timing = {}
        for name in order:
            start = time.perf_counter()
            ss = regina.NormalSurfaces(triangulation,regina.NormalCoords.Standard,
                                       which,arms[name])
            timing[name] = time.perf_counter()-start
            assert vector_set(ss) == vectors["regina_default"]
        samples.append({"repeat": repeat,"order": order,"seconds": timing})
    return {
        "scope": "full standard-coordinate embedded vertex enumeration only",
        "warmups_seconds": warmups,"actual_algorithms": actual,
        "samples": samples,
        "median_seconds": {name:statistics.median(s["seconds"][name] for s in samples)
                           for name in arms},
        "identical_vector_sets": True,
    }


def audit(name,t,recipe,repeats,rng):
    assert t.isValid() and t.isOrientable() and t.isConnected()
    assert not t.isIdeal() and t.countBoundaryComponents() == 1
    assert t.boundaryComponent(0).eulerChar() == 0
    start = time.perf_counter()
    ss = regina.NormalSurfaces(t,regina.NormalCoords.Standard)
    enumeration_seconds = time.perf_counter()-start
    native_qmatrix = regina.makeMatchingEquations(t,regina.NormalCoords.Quad)
    qmatrix = [[integer(native_qmatrix.entry(i,j)) for j in range(native_qmatrix.columns())]
               for i in range(native_qmatrix.rows())]
    records = [surface_record(s,qmatrix) for s in ss]
    qs = regina.NormalSurfaces(t,regina.NormalCoords.Quad)
    qrecords = [surface_record(s,qmatrix) for s in qs]
    discs = [i for i,s in enumerate(records) if s["essential_disc"]]
    qdiscs = [i for i,s in enumerate(qrecords) if s["essential_disc"]]
    assert bool(discs) == recipe.get("has_essential_disc",recipe["type"] == "solid_torus")
    report = {
        "id": name,"recipe": recipe,"isosig": t.isoSig(),
        "tetrahedra": t.size(),"vertices": t.countVertices(),
        "boundary_triangles": t.countBoundaryTriangles(),
        "boundary_components": t.countBoundaryComponents(),
        "valid": True,"orientable": True,"compact": True,
        "triangulation": export(t),
        "quad_matching_equations":qmatrix,
        "standard_vertex_count": ss.size(),
        "quad_vertex_count": qs.size(),
        "standard_support_histogram": support_histogram(ss),
        "quad_support_histogram": support_histogram(qs),
        "standard_essential_disc_indices": discs,
        "quad_essential_disc_indices": qdiscs,
        "minimum_standard_disc_support": min((records[i]["quadrilateral_support"]
                                               for i in discs),default=None),
        "minimum_quad_disc_support": min((qrecords[i]["quadrilateral_support"]
                                           for i in qdiscs),default=None),
        "standard_vertices": records,"quad_vertices": qrecords,
        "first_enumeration_seconds": enumeration_seconds,
        "benchmark": benchmark_enumeration(t,repeats,rng),
    }
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
    ap.add_argument("--repeats",type=int,default=5)
    ap.add_argument("--only",nargs="*")
    args = ap.parse_args()
    rng = random.Random(SEED)
    results = {"schema":"normal-disc-discovery-corpus-v1","seed":SEED,
        "regina_version":regina.versionString(),"python":platform.python_version(),
        "platform":platform.platform(),"repeats":args.repeats,
        "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"external oracle corpus; no complete recognizer benchmark",
        "records":[]}
    for name,t,recipe in fixtures():
        if args.only and name not in args.only:
            continue
        record = audit(name,t,recipe,args.repeats,rng)
        results["records"].append(record)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(results,indent=2)+"\n")
        print(name,t.size(),record["standard_vertex_count"],
              record["quad_vertex_count"],record["minimum_standard_disc_support"],
              record["minimum_quad_disc_support"],flush=True)


if __name__ == "__main__":
    main()
