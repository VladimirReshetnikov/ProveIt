#!/usr/bin/env python3
"""Small independent checker for the PA194 -> PA194B finite-run certificate.

Standard library only. This program imports neither the builder nor its
symbolic runtime. The four exceptional cases use a partial tape whose reads
outside {-1,0} are forbidden. Thus each case checks an exact identity with
arbitrary exterior tape, rather than sampling exterior tape values.

The general finite-run induction is written in report/pa194_report.tex.
Checking this certificate is not an end-to-end formalization of Con(PA).
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OLD_SHA = "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"
PRIMARY_DENSE_SHA = "4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f"
NEW_SHA = "b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    table = {}
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, f"{path.name}:{line_no}: bad row")
        q, b, w, direction, target = fields
        q, b, w, target = map(int, (q, b, w, target))
        require(b in (0, 1) and w in (0, 1), "Not binary")
        require(direction in ("L", "R"), "Non-unit movement")
        require((q, b) not in table, "Duplicate transition")
        table[q, b] = (w, -1 if direction == "L" else 1, target)
    states = {q for q, b in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)},
            "Incomplete working-state table")
    halts = {a[2] for a in table.values()} - states
    require(len(halts) == 1, "Expected one terminal halt label")
    return table, states, next(iter(halts))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reachable(table, start, halt):
    seen = {start}
    todo = [start]
    for q in todo:
        for b in (0, 1):
            n = table[q, b][2]
            if n != halt and n not in seen:
                seen.add(n)
                todo.append(n)
    return seen


def check(output=None):
    old_path = ROOT / "inputs/pa194.native.tm"
    dense_path = ROOT / "machine/pa194B.tm"
    require(sha(old_path) == OLD_SHA, "Pinned input hash mismatch")
    require(sha(dense_path) == NEW_SHA, "Dense output hash mismatch")
    old, old_states, old_halt = read_table(old_path)
    primary_path = ROOT / "inputs/primary_dense.tm"
    require(sha(primary_path) == PRIMARY_DENSE_SHA, "Pinned primary dense hash mismatch")
    primary, primary_states, primary_halt = read_table(primary_path)
    primary_labels = json.loads((ROOT / "inputs/primary_labels.json").read_text())
    require(primary_states == set(range(194)) and primary_halt == 194,
            "Bad primary dense numbering")
    require(len(primary_labels) == len(set(primary_labels)) == 195
            and primary_labels[0] == 74 and primary_labels[-1] == old_halt
            and set(primary_labels[:-1]) == old_states,
            "Bad primary dense/native label bijection")
    for (q, b), (w, d, n) in primary.items():
        require(old[primary_labels[q], b] == (w, d, primary_labels[n]),
                "Pinned primary does not reconstruct the native input")
    new, new_states, new_halt = read_table(ROOT / "machine/pa194B.native.tm")
    dense, dense_states, dense_halt = read_table(dense_path)
    require(old_states == new_states and len(new_states) == 194,
            "State set/count mismatch")
    require(old_halt == new_halt == 254, "Native halt label mismatch")
    require(dense_states == set(range(194)) and dense_halt == 194,
            "Dense numbering mismatch")
    require(reachable(new, 74, 254) == new_states, "Unreachable working state")

    expected_changes = {
        (87, 0): ((0, 1, 301), (0, 1, 88)),
        (88, 0): ((0, 1, 122), (0, -1, 301)),
        (301, 0): ((0, 1, 45), (0, 1, 122)),
        (301, 1): ((1, 1, 103), (1, 1, 301)),
    }
    changes = {k: (old[k], new[k]) for k in old if old[k] != new[k]}
    require(changes == expected_changes, "The four-row delta does not match")
    incoming = {
        target: sorted((q, b, w, d) for (q, b), (w, d, n) in old.items()
                       if n == target)
        for target in (88, 301)
    }
    require(incoming == {88: [(77, 1, 1, 1)], 301: [(87, 0, 0, 1)]},
            "Unaccounted incoming history")
    require(74 not in (88, 301), "Initial history would be unconstrained")

    # Every ordinary transition respects the control map rho(301)=88.
    rho = lambda q: 88 if q == 301 else q
    ordinary = 0
    for (q, b), (w, d, n) in old.items():
        if q in (88, 301):
            continue
        require(new[rho(q), b] == (w, d, rho(n)),
                f"Ordinary-step mismatch at {q}/{b}")
        ordinary += 1

    cases = []
    for old_state, history in ((88, 1), (301, 0)):
        for bit in (0, 1):
            cells = {-1: history, 0: bit}
            w, d, n = old[old_state, bit]
            final_cells = {-1: history, 0: w}
            goal = (rho(n), d, final_cells)
            q, h = rho(old_state), 0
            trace = [(q, h, dict(cells))]
            for steps in range(1, 6):
                require(h in cells, "Local proof tried to read arbitrary exterior")
                require(q != 254, "Premature halt in a local segment")
                w, d, q = new[q, cells[h]]
                cells[h] = w
                h += d
                trace.append((q, h, dict(cells)))
                if (q, h, cells) == goal:
                    break
            else:
                raise ValueError("Local identity did not close in five steps")
            expected_duration = 1 if bit else (3 if old_state == 88 else 5)
            require(steps == expected_duration, "Unexpected duration")
            cases.append(dict(old_control=old_state, history=history,
                              read=bit, duration=steps, trace=trace))

    # Exact conjugacy of the supplied native and dense transition files.
    labels = json.loads((ROOT / "machine/pa194B.labels.json").read_text())
    require(len(labels) == 195 and labels[0] == 74 and labels[-1] == 254,
            "Bad label list endpoints")
    require(len(set(labels)) == 195 and set(labels[:-1]) == new_states,
            "Label list is not a bijection")
    for (q, b), (w, d, n) in dense.items():
        require(new[labels[q], b] == (w, d, labels[n]),
                "Dense/native conjugacy failed")

    # A directly inspectable graph invariant proves novelty against every
    # recognized prior 194-state class. Reuse all 82 complete literal tables.
    frontier = json.loads((ROOT / "comparison/frontier194.json").read_text())
    loop_counts = []
    for item in frontier["classes"]:
        path = ROOT / "comparison/frontier_tables" / (item["graph_hash"] + ".tm")
        rows, states, halt = read_table(path)
        require(len(states) == 194, "Bad frontier representative")
        count = sum(q == a[2] for (q, b), a in rows.items())
        require(count == 21, "A prior graph does not have 21 self loops")
        loop_counts.append(count)
    new_loops = sum(q == a[2] for (q, b), a in new.items())
    require(len(loop_counts) == 82 and new_loops == 22, "Novelty invariant failed")

    result = {
        "ok": True,
        "pinned_input_sha256": OLD_SHA,
        "pinned_primary_dense_sha256": PRIMARY_DENSE_SHA,
        "pinned_primary_native_reconstruction": True,
        "dense_output_sha256": NEW_SHA,
        "working_states": 194,
        "transition_rows": 388,
        "all_states_graph_reachable": True,
        "ordinary_transition_cases": ordinary,
        "exceptional_transition_cases": cases,
        "arbitrary_exterior_tape_not_read": True,
        "native_dense_conjugacy": True,
        "time_bound": "t <= t_B = t + 2*a_t + 4*b_t <= 5*t",
        "prior_194_graphs_compared": 82,
        "prior_self_loop_counts": sorted(set(loop_counts)),
        "new_self_loop_count": new_loops,
        "scope": "Finite local certificate plus the report's induction proves halting transfer; the inherited PA calibration remains a separate dependency.",
    }
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.output)
    print(json.dumps({k: v for k, v in result.items()
                      if k != "exceptional_transition_cases"}, indent=2))
