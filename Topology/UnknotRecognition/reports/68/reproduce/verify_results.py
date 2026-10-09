"""Independently replay the retained research witnesses from this package."""
from collections import Counter
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import platform
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / "fast"
sys.path.insert(0, str(FAST))
from fastunknot import Diagram
from fastunknot.integer_codec import json_safe, encoded_integer
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.pachner32_verify import verify_pachner_32
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.marked_boundary_verify import verify_marked_boundary_certificate
from fastunknot.interval_orbits import IntervalPairing


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def read(path):
    return json.loads(path.read_text())


def digest(value):
    return sha256(json.dumps(json_safe(value), sort_keys=True,
                             separators=(",", ":")).encode()).hexdigest()


def checked_transport_chain(raw, heights, steps):
    for step in steps:
        require(verify_cocycle_transport(raw, heights, step["triangulation"],
                                        step["transport"]), "transport replay")
        raw, heights = step["triangulation"], step["transport"]["heights"]
    return raw, heights


def scalar_audit():
    count = 0
    span = lambda *values: max(values)-min(values)
    for heights in product(range(-3,4),repeat=5):
        c,d,e,A,B = heights
        x,y,z = sorted((c,d,e))
        L,U = sorted((A,B))
        gap = max(0,L-z)+max(0,x-U)
        delta = (max(U,y)-min(L,y)+max(0,min(U,x)-L)+max(0,U-max(L,z)))
        direct = (span(A,B,c,d)+span(A,B,d,e)+span(A,B,e,c)
                  -span(A,c,d,e)-span(B,c,d,e))
        euler = direct-span(A,B,c)-span(A,B,d)-span(A,B,e)+span(c,d,e)+abs(A-B)
        require(delta==direct and euler==-2*gap, "five-height identity")
        count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT/"reproduced/retained_proof_replay.json")
    args = parser.parse_args()
    start = time.perf_counter()
    scalar_cases = scalar_audit()
    corpus = read(ROOT/"synthesis/data/cocycle-transport-corpus.json")
    schemas = Counter()
    for key, proof in corpus["proofs"].items():
        require(digest(proof)==key, "retained proof digest")
        schemas[proof["schema"]] += 1
        diagram = Diagram.from_pd(proof["input_pd"])
        if proof["schema"] == "diagram-transport-disc-v1":
            require(verify_transport_disk_certificate(diagram, proof),
                    "source-bound transport witness")
        elif proof["schema"] == "diagram-regauge-research-v1":
            raw = proof["source_triangulation"]
            require(verify_diagram_exterior(diagram, raw), "reference source exterior")
            for step in proof["moves"]:
                require(verify_pachner_32(raw, step["triangulation"], step["move"]),
                        "reference move")
                raw = step["triangulation"]
            require(verify_normal_disk_count_certificate(
                raw, proof["coordinates"], proof["disk_certificate"]),
                "reference terminal disc")
            require(encoded_integer(proof["disk_certificate"]["compressing_disk_components"])>0,
                    "reference disc count must be positive")
        else:
            raise AssertionError("Unknown research bundle schema")
    records = corpus["records"]
    require(len(records)==82, "corpus size")
    positives, collapses, totals = {}, {}, {}
    for arm in ("first-regauge","first-transport","score-transport"):
        require(all(r["arms"][arm]["status"]=="COMPLETE" for r in records), "complete corpus arm")
        positives[arm] = sum(r["arms"][arm]["compressing_disks"]>0 for r in records)
        collapses[arm] = sum(r["arms"][arm]["stats"]["moves"] for r in records)
        totals[arm] = sum(r["arms"][arm]["normal_disks"] for r in records)
        require(positives[arm]==15 and collapses[arm]==144, "corpus counts")
    for record in records:
        arms = record["arms"]
        require(len({a["euler"] for a in arms.values()})==1, "corpus Euler equality")
        require(arms["first-transport"]["normal_disks"]==arms["score-transport"]["normal_disks"],
                "transport policy piece equality")
        for arm in ("first-transport","score-transport"):
            if arms[arm]["compressing_disks"]:
                require(arms[arm]["source_certificate_verified"], "source replay record")
                require(arms[arm]["proof_sha256"] in corpus["proofs"], "positive proof present")

    local = read(ROOT/"synthesis/data/cocycle-transport-local.json")
    obstruction = local["obstruction"]
    raw, heights = checked_transport_chain(
        obstruction["source_triangulation"], obstruction["source_heights"],
        obstruction["descent"]["moves"])
    require(raw==obstruction["descent"]["triangulation"], "obstruction final state")
    require(verify_normal_disk_count_certificate(raw, obstruction["descent"]["coordinates"],
                                                obstruction["disk_certificate"]), "obstruction disc")
    require(len(raw["tetrahedra"])==2 and len(obstruction["descent"]["moves"])==6,
            "obstruction size and moves")

    split = read(ROOT/"synthesis/data/cocycle-transport-splitting.json")
    before, hbefore = checked_transport_chain(split["initial_triangulation"],
                                              split["initial_heights"], [split["preparation"]])
    after, hafter = checked_transport_chain(before, hbefore, [split["collapse"]])
    require(verify_normal_component_certificate(
        before, split["preparation"]["transport"]["coordinates"],
        split["before_census"]["certificate"]), "splitting before census")
    require(verify_normal_component_certificate(
        after, split["collapse"]["transport"]["coordinates"],
        split["after_census"]["certificate"]), "splitting after census")
    require(split["before_census"]["components"]==1 and split["after_census"]["components"]==3,
            "splitting component counts")

    matched = read(FAST/"marked_boundary_research/measurements_matched_final.json")
    source = matched["native_source"]
    pairings = [IntervalPairing(*row[:4], reverse=(row[4]==-1)) for row in source["pairings"]]
    boundary_proofs = 0
    for case in matched["cases"]:
        for encoding, proof in case["reference_certificates"].items():
            require(verify_marked_boundary_certificate(
                source["points"], pairings, case["marks"], proof,
                start_half_edge=case["start_half_edge"], weight_encoding=encoding),
                "marked boundary reference replay")
            require(proof["solution"]==case["exact_output"], "boundary full solution")
            boundary_proofs += 1
        a,b = (case["reference_certificates"][s]["weighted_proof"]["orbit_proof"]
               for s in ("moments","one_hot"))
        require(a==b, "identical full AHT proof")
        require(case["all_six_outputs_and_orbit_proofs_identical"], "matched observation record")

    measured_hashes = 0
    score = read(ROOT/"synthesis/data/cocycle-transport-benchmark.json")
    for path, expected in score["source_sha256"].items():
        require(sha256((ROOT/path).read_bytes()).hexdigest()==expected, "scoring measured source")
        measured_hashes += 1
    for path, expected in matched["source_sha256"].items():
        require(sha256((FAST/path).read_bytes()).hexdigest()==expected, "boundary measured source")
        measured_hashes += 1
    with zipfile.ZipFile(FAST/"transport_research/measured_sources_before_callback_fix.zip") as old:
        for filename in ("cocycle-transport-local.json","cocycle-transport-corpus.json",
                         "cocycle-transport-benchmark-pre-callback.json"):
            data = read(ROOT/"synthesis/data"/filename)
            for path, expected in data["source_sha256"].items():
                require(sha256(old.read(path)).hexdigest()==expected, "historical measured source")
    result = {
        "schema":"retained-proof-replay-v1", "status":"PASS",
        "python":platform.python_version(), "scalar_height_cases":scalar_cases,
        "corpus_sources":len(records), "corpus_positive_bundles":dict(schemas),
        "positive_runs_per_arm":positives, "collapses_per_arm":collapses,
        "piece_totals_per_arm":totals,
        "obstruction_moves":6, "splitting_component_counts":[1,3],
        "matched_boundary_reference_certificates":boundary_proofs,
        "final_measured_source_hashes_checked":measured_hashes,
        "historical_measurement_sources_checked":True,
        "elapsed_seconds":time.perf_counter()-start,
        "verifier_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Native independent replay and exact arithmetic; timings here are verification cost, not benchmarks."
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
