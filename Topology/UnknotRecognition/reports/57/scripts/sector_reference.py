#!/usr/bin/env python3
"""Select independent Regina oracle cases for a supplied quadrilateral sector.

Allowed types use -1 for no quadrilateral in a tetrahedron, otherwise 0,1,2.
Every expected vector is obtained by filtering a COMPLETE Regina enumeration,
not by a producer's matching equations or potential reduction.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path

from discovery_corpus import matrix_rank


def supports(surface,types):
    return all(not value or types[t] == q
               for t,row in enumerate(surface["coordinates"])
               for q,value in enumerate(row[4:]))


def occupied_types(surface):
    return tuple(next((q for q in range(3) if row[4+q]),-1)
                 for row in surface["coordinates"])


def kernel_dimension(record,types):
    columns = [3*t+q for t,q in enumerate(types) if q>=0]
    return len(columns)-matrix_rank([
        [row[c] for c in columns] for row in record["quad_matching_equations"]])


def cases_for(record):
    t = record["tetrahedra"]
    if t<=3:
        return [(types,"exhaustive_small") for types in product([-1,0,1,2],repeat=t)]
    chosen = {}
    for surface in record["standard_vertices"]:
        if not surface["quadrilateral_support"]:
            continue
        pattern = occupied_types(surface)
        if surface["occupied_sector_kernel_dimension"]<=2:
            chosen[pattern] = "vertex_occupied_d_le_2"
    # Full type sectors of essential meridians exercise dense supports.
    for index in record["standard_essential_disc_indices"]:
        surface = record["standard_vertices"][index]
        pattern = tuple(surface["full_sector_quad_types"])
        if surface["full_sector_kernel_dimension"]<=3:
            chosen[pattern] = "full_disc_sector"
    # One d=3 occupied sector per triangulation gives a limited harder control.
    for surface in record["standard_vertices"]:
        if surface["occupied_sector_kernel_dimension"]==3:
            chosen.setdefault(occupied_types(surface),"selected_vertex_d_3")
            break
    chosen.setdefault(tuple(-1 for _ in range(t)),"empty_sector")
    return [(k,chosen[k]) for k in sorted(chosen)]


def reference_case(record,types,selection):
    standard = [i for i,s in enumerate(record["standard_vertices"])
                if s["quadrilateral_support"] and supports(s,types)]
    quad = [i for i,s in enumerate(record["quad_vertices"]) if supports(s,types)]
    spositive = any(record["standard_vertices"][i]["euler_characteristic"]>0 for i in standard)
    qpositive = any(record["quad_vertices"][i]["euler_characteristic"]>0 for i in quad)
    assert spositive == qpositive, (record["id"],types,spositive,qpositive)
    discs = [i for i in standard if record["standard_vertices"][i]["essential_disc"]]
    return {
        "fixture_id":record["id"],"types":list(types),"selection":selection,
        "kernel_dimension":kernel_dimension(record,types),
        "standard_indices":standard,"quad_indices":quad,
        "standard_positive_euler_exists":spositive,
        "quad_positive_euler_exists":qpositive,
        "standard_essential_disc_indices":discs,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus",type=Path,default=Path(__file__).with_name("discovery_corpus.json"))
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("sector_cases.json"))
    args = ap.parse_args()
    data = json.loads(args.corpus.read_text())
    cases = [reference_case(r,types,selection) for r in data["records"]
             for types,selection in cases_for(r)]
    result = {
        "schema":"normal-sector-regina-reference-v1",
        "corpus_sha256":hashlib.sha256(args.corpus.read_bytes()).hexdigest(),
        "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "case_count":len(cases),
        "selection_counts":dict(Counter(c["selection"] for c in cases)),
        "kernel_dimension_histogram":dict(sorted(Counter(c["kernel_dimension"] for c in cases).items())),
        "positive_euler_equivalence_all_cases":True,
        "positive_euler_without_essential_standard_disc":sum(
            c["standard_positive_euler_exists"] and not c["standard_essential_disc_indices"]
            for c in cases),
        "cases":cases,
    }
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="cases"},indent=2))


if __name__ == "__main__":
    main()
