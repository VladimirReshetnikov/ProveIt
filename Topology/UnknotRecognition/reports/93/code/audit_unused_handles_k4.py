"""Audit local characteristic graphs after the unused-handle compiler.

This finite source audit supports the local-template proof; it is not the
proof for all triangulations.  Cancellation/decomposition certificates are
checked by the independent geometric verifier before the local graphs are
assembled from the maintained native edge-link sectors.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE / "native_snapshot"))

from fastunknot.normal_surface_geometry import _prepare
from fastunknot.source_handle_reduction import _source_handles
from unused_handles import decompose_unused_handles, verify_unused_handle_certificate


def audit(corpus_path):
    corpus_bytes = Path(corpus_path).read_bytes()
    corpus = json.loads(corpus_bytes)
    results = []
    totals = Counter()
    for record in corpus["records"]:
        triangulation = record["triangulation"]
        packet = decompose_unused_handles(triangulation)
        if packet["status"] != "DECOMPOSED" or not verify_unused_handle_certificate(
            triangulation, packet["certificate"]
        ):
            raise AssertionError((record["id"], "geometric certificate rejected"))
        prepared = _prepare(triangulation, lambda: None)
        handles = _source_handles(prepared, lambda: None)
        remaining = packet["reduction_certificate"]["remaining"]
        alive_one = set(remaining["one_handles"])
        alive_two = set(remaining["two_handles"])
        degrees = Counter()
        for handle in handles["two_handles"]:
            if handle["id"] in alive_two:
                degrees.update(x["one_handle"] for x in handle["attaching_cycle"])

        owner = {}
        for handle in handles["one_handles"]:
            owner[(handle["tetrahedron"], handle["face"])] = handle["id"]
            owner[(handle["target_tetrahedron"], handle["target_face"])] = handle["id"]
        graphs = {t: {} for t in range(handles["zero_handles"])}
        for (t, face), handle in owner.items():
            if handle in alive_one and degrees[handle] > 0:
                graphs[t][face] = set()
        for handle in handles["two_handles"]:
            if handle["id"] not in alive_two:
                continue
            for sector in handle["sectors"]:
                t, a, b = (sector[key] for key in ("tetrahedron", "entry_face", "exit_face"))
                graph = graphs[t]
                if a == b or a not in graph or b not in graph or b in graph[a]:
                    raise AssertionError((record["id"], "not a simple local graph", t, a, b))
                graph[a].add(b)
                graph[b].add(a)

        local_results = []
        for t, graph in graphs.items():
            if not graph:
                continue
            if len(graph) > 4:
                raise AssertionError((record["id"], "too many local ports", t))
            for face, neighbours in graph.items():
                if len(neighbours) != degrees[owner[(t, face)]] or len(neighbours) < 2:
                    raise AssertionError((record["id"], "local/global degree mismatch", t, face))
            reached, todo = set(), [next(iter(graph))]
            while todo:
                face = todo.pop()
                if face not in reached:
                    reached.add(face)
                    todo.extend(graph[face] - reached)
            if len(reached) != len(graph):
                raise AssertionError((record["id"], "disconnected characteristic graph", t))
            degree_sequence = sorted(map(len, graph.values()))
            signature = f"{len(graph)} ports; degrees {','.join(map(str, degree_sequence))}"
            totals[signature] += 1
            local_results.append({
                "zero_handle": t,
                "ports": sorted(graph),
                "edges": [[a, b] for a in sorted(graph) for b in sorted(graph[a]) if a < b],
                "degree_sequence": degree_sequence,
                "connected": True,
            })
        results.append({
            "source_id": record["id"],
            "tetrahedra": len(triangulation["tetrahedra"]),
            "torus_case": packet["torus_case"],
            "nonempty_characteristic_graphs": local_results,
        })
    return {
        "schema": "unused-handles-k4-audit-v1",
        "source_commit": corpus["source_commit"],
        "corpus_sha256": hashlib.sha256(corpus_bytes).hexdigest(),
        "source_count": len(results),
        "nonempty_graph_count": sum(totals.values()),
        "signature_counts": dict(sorted(totals.items())),
        "all_local_checks_passed": True,
        "scope": "Finite source audit; the general result follows from the tetrahedral K4 template proof.",
        "records": results,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=PACKAGE / "data" / "unused_handles_source_corpus.json")
    parser.add_argument("--output", type=Path, default=PACKAGE / "data" / "unused_handles_k4_audit.json")
    args = parser.parse_args()
    result = audit(args.corpus)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "source_count", "nonempty_graph_count", "signature_counts", "all_local_checks_passed"
    )}, sort_keys=True))


if __name__ == "__main__":
    main()
