"""Independently replay the six finite, free-exterior local certificates."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        state, read, write, move, successor = line.split()
        key = int(state), int(read)
        assert key not in result and move in ("L", "R")
        result[key] = int(write), (-1 if move == "L" else 1), int(successor)
    return result


def mapped(q):
    return 80 if q == 169 else q


def replay(table, state, assumptions, transcript):
    position = 0
    tape = dict(assumptions)
    for row in transcript:
        assert row["state"] == state and row["head"] == position
        value = tape.get(position, ("independent_original_bit", position))
        assert value in (0, 1), "Transcript reads an unconstrained exterior cell."
        assert row["read"] == value
        write, move, successor = table[state, value]
        assert (row["write"], row["direction"], row["next"]) == (write, move, successor)
        tape[position] = write
        position += move
        state = successor
        assert state != 254, "No local block has an intermediate halt."
    return state, position, tape


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, default=ROOT / "ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-rotation240/zfc_rotation240_old.tm")
    parser.add_argument("--candidate", type=Path, default=HERE / "candidate239_boot/candidate239_v106_old.tm")
    parser.add_argument("--certificate", type=Path, default=ROOT / "state_folds/local239_certificate.json")
    parser.add_argument("--output", type=Path, default=HERE / "local239_independent_review.json")
    args = parser.parse_args()
    assert __debug__
    old, new = read_table(args.baseline), read_table(args.candidate)
    certificate = json.loads(args.certificate.read_text())
    for table, count in ((old, 240), (new, 239)):
        states = {q for q, _ in table}
        assert len(states) == count and len(table) == count * 2
        assert all((q, b) in table for q in states for b in (0, 1))
        assert {t for _, _, t in table.values()} - states == {254}
    for row, result in old.items():
        q, read = row
        if q in (80, 91, 169):
            continue
        write, move, target = result
        assert new[mapped(q), read] == (write, move, mapped(target))
    assert new[80, 0] == (0, -1, 106) and new[80, 1] == (1, 1, 91)
    assert new[91, 0] == (0, 1, 106) and new[91, 1] == (1, -1, 167)

    # Reconstruct the inductive structural predicate independently of the JSON.
    predicate = {67: {-1: 0}, 80: {-2: 0, -1: 1}, 91: {-3: 0, -2: 1, -1: 1}, 169: {-1: 0}}
    assert 95 not in predicate
    preservation = []
    for (q, bit), (write, move, target) in old.items():
        if target not in predicate:
            continue
        known = {**predicate.get(q, {}), 0: write}
        for relative, required in predicate[target].items():
            assert known.get(relative + move) == required
        preservation.append([q, bit, target])

    expected = {
        "80/read0": (80, {-1: 1, 0: 0}, 1, 5),
        "80/read1": (80, {0: 1}, 1, 1),
        "169/read0": (169, {-1: 0, 0: 0}, 1, 3),
        "169/read1": (169, {-1: 0, 0: 1, 1: 1}, 1, 5),
        "91/read0": (91, {0: 0}, 1, 1),
        "91/read1": (91, {-3: 0, -2: 1, -1: 1, 0: 1}, 3, 11),
    }
    assert len(certificate["cases"]) == 6
    reviewed = []
    for case in certificate["cases"]:
        state, assumptions, old_steps, new_steps = expected.pop(case["name"])
        assert case["old_state"] == state and case["new_state"] == mapped(state)
        assert {int(k): v for k, v in case["assumptions"].items()} == assumptions
        assert len(case["old_trace"]) == case["old_steps"] == old_steps
        assert len(case["new_trace"]) == case["new_steps"] == new_steps
        before = replay(old, state, assumptions, case["old_trace"])
        after = replay(new, mapped(state), assumptions, case["new_trace"])
        assert mapped(before[0]) == after[0] and before[1] == after[1]
        for p in before[2].keys() | after[2].keys():
            free = ("independent_original_bit", p)
            assert before[2].get(p, free) == after[2].get(p, free)
        reviewed.append({"case": case["name"], "old_steps": old_steps, "new_steps": new_steps, "endpoint": list(after[:2])})
    assert not expected
    report = {
        "status": "INDEPENDENT_FREE_EXTERIOR_CERTIFICATE_REPLAY_PASS",
        "baseline_sha256": hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        "candidate_sha256": hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        "certificate_sha256": hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
        "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "working_states_before": 240,
        "working_states_after": 239,
        "complete_transition_domains_checked": True,
        "all_other_rows_match_under_state_map": True,
        "structural_invariant_incoming_rows": preservation,
        "local_cases": reviewed,
        "semantic_premise": "In the old reachable run, q169/read1 implies a 1 immediately to the right; established separately by the all-case symbolic guard audit.",
        "conclusion": "Conditional on that semantic premise, every old reachable configuration has a positive finite block simulation under 169->80, preserving the complete tape, head, and halting equivalence. No new-run invariant is required: invariants are used only at mapped old configurations.",
        "halting_argument": "Every local old block and new block has positive length and no intermediate halt. Unchanged steps also take one step. Thus an infinite old execution yields an infinite new execution, and an old finite halting execution yields a new finite halting execution. Determinism supplies the equivalence.",
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
