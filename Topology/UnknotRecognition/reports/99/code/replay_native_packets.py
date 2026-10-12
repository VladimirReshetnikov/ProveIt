"""Replay the seven positive and three restricted negative native packets.

Requires an unpacked ProveIt checkout with the accompanying native patch.
No Regina dependency, surface discovery, or proof producer is used here.
"""

import argparse
import json
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="root of the patched ProveIt checkout")
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    fast = args.repo.resolve() / "Topology/UnknotRecognition/fast"
    require((fast / "fastunknot/normal_cut_dual_verify.py").is_file(),
            "the native patch is missing from this checkout")
    sys.path[:0] = [str(fast), str(package / "code/forest_search")]

    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
    from source_core_dual_research.audit_obstructions import reconstruct
    from dual_forest_verify import check_result

    positives = sorted((package / "results/native/certificates").glob("*.json"))
    negatives = sorted(p for p in (package / "results/native/obstructions").glob("*.json")
                       if p.name != "obstruction_audit.json")
    require(len(positives) == 7, "expected seven positive source packets")
    require(len(negatives) == 3, "expected three negative source packets")
    verified_positive, verified_negative = [], []
    for path in positives:
        packet = json.loads(path.read_text())
        require(verify_normal_cut_handlebodies(packet["triangulation"], packet["coordinates"],
                                              packet["certificate"]),
                "positive source replay failed: " + packet["id"])
        verified_positive.append(packet["id"])

    for path in negatives:
        packet = json.loads(path.read_text())
        raw, coordinates = packet["triangulation"], packet["coordinates"]
        require(verify_normal_cut_parallelity(raw, coordinates, packet["parallelity"]),
                "source geometry authentication failed: " + packet["id"])
        require(verify_parallelity_boundary_words(raw, coordinates, packet["boundary"]),
                "source boundary authentication failed: " + packet["id"])
        problem, row_ids, forest = reconstruct(packet, packet["parallelity"]["geometry"],
            packet["parallelity"]["summary"], packet["boundary"]["skeleton"])
        require(problem == packet["problem"], "independent matrix reconstruction disagrees")
        require(row_ids == packet["original_row_ids"], "source row identity disagrees")
        require(forest == packet["source_forest"], "fixed 0/1 forest disagrees")
        require(packet["result"]["status"] == "NO_FOREST", "unexpected negative status")
        accepted, reason = check_result(problem, packet["result"])
        require(accepted, reason)
        verified_negative.append(packet["id"])

    print(json.dumps({
        "all_passed": True,
        "native_positive_packets": verified_positive,
        "source_authenticated_restricted_negative_packets": verified_negative,
        "negative_scope": "No dual forest makes the fixed raw finite boundary kernel completely eliminable; no non-handlebody or knottedness conclusion."
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
