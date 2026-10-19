"""Independent reconstruction and two-interpreter blank bootstrap certificate.

Only this finite prefix is verified here.  The separate universal runtime
argument is needed to conclude the unbounded simulation theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEFAULT = ROOT / "ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-rotation240/zfc_rotation240_old.tm"


def parse(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, target = line.split()
            key = int(q), int(b)
            assert key not in rows
            assert d in ("L", "R")
            rows[key] = int(w), (1 if d == "R" else -1), int(target)
    assert start == 95
    return rows


def write_table(path, rows, canonical=False):
    states = sorted({q for q, _ in rows})
    assert len(states) == 239 and len(rows) == 478
    assert {t for _, _, t in rows.values()} - set(states) == {254}
    order = [95] + [q for q in states if q != 95]
    rename = dict(zip(order, range(239))) if canonical else {q: q for q in states}
    rename[254] = 239 if canonical else 254
    lines = ["#! start " + str(rename[95])]
    normalized = {(rename[q], b): (w, d, rename[t]) for (q, b), (w, d, t) in rows.items()}
    for (q, b), (w, d, t) in sorted(normalized.items()):
        lines.append(f"{q} {b} {w} {'R' if d == 1 else 'L'} {t}")
    path.write_text("\n".join(lines) + "\n")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def desired_ones():
    # Literal complete-frame construction, independent of either interpreter.
    ones = {-6, 176}
    p = 177
    for value in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
        p += 1
        for i in range(value + 1):
            ones.add(p + i)
        p += value + 1
    return frozenset(ones)


def sparse(rows, target, fuel):
    tape = set()
    q = 95
    head = 0
    lower = upper = head
    q96_entries = 0
    special = {80: 0, 91: 0, 169: 0}
    for tick in range(fuel + 1):
        if q == 96:
            q96_entries += 1
            if head == -5 and tape == target:
                return tick, q, head, frozenset(tape), (lower, upper), q96_entries, special
        assert q != 254, ("premature halt", tick, head)
        if q in special:
            special[q] += 1
        read = int(head in tape)
        write, move, q = rows[q, read]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += move
        lower = min(lower, head)
        upper = max(upper, head)
    raise AssertionError(("bootstrap fuel", fuel, q, head, len(tape)))


def dense(rows, clock):
    # Independent storage, indexing, dispatch, transition loop and stop rule.
    offset = 4096
    cells = bytearray(8192)
    instruction = [[None, None] for _ in range(1 + max({q for q, _ in rows} | {t for _, _, t in rows.values()}))]
    for (source, symbol), (write, move, target) in rows.items():
        instruction[source][symbol] = write, move, target
    state = 95
    position = offset
    leftmost = rightmost = position
    for _ in range(clock):
        assert 0 <= position < len(cells)
        entry = instruction[state][cells[position]]
        assert entry is not None
        cells[position] = entry[0]
        position += entry[1]
        state = entry[2]
        leftmost = min(leftmost, position)
        rightmost = max(rightmost, position)
    ones = frozenset(i - offset for i, x in enumerate(cells) if x)
    return state, position - offset, ones, (leftmost - offset, rightmost - offset)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, default=DEFAULT)
    parser.add_argument("--output", type=Path, default=HERE / "candidate239_boot")
    parser.add_argument("--fuel", type=int, default=1000000)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    baseline = parse(args.baseline)
    target = desired_ones()
    assert len(target) == 351
    reports = []
    for variant in (106, 12, 142):
        rows = baseline.copy()
        assert rows[147, 0] == (0, 1, 169)
        assert [k for k, v in rows.items() if v[2] == 169] == [(147, 0)]
        rows[147, 0] = 0, 1, 80
        rows[80, 0] = 0, -1, variant
        rows[91, 1] = 1, -1, 167
        del rows[169, 0]
        del rows[169, 1]
        edits = [[*key, list(baseline[key]), list(value)] for key, value in sorted(rows.items()) if value != baseline[key]]
        assert [r[:2] for r in edits] == [[80, 0], [91, 1], [147, 0]]
        old_path = args.output / f"candidate239_v{variant}_old.tm"
        canonical_path = args.output / f"candidate239_v{variant}.tm"
        old_hash = write_table(old_path, rows)
        canonical_hash = write_table(canonical_path, rows, canonical=True)
        # Independent agent's supplied tables are only a cross-check, never input.
        supplied = ROOT / f"state_folds/candidate239_169_80_v{variant}_old.tm"
        supplied_match = parse(supplied) == rows if supplied.exists() else None
        assert supplied_match is not False
        tick, state, head, ones, visited, q96_entries, special = sparse(rows, target, args.fuel)
        assert dense(rows, tick) == (state, head, ones, visited)
        assert state == 96 and head == -5 and ones == target
        report = {
            "status": "TWO_INTERPRETER_EXACT_BLANK_BOOT_PASS",
            "variant": variant,
            "working_states": 239,
            "transition_rows": 478,
            "halt_state_old": 254,
            "halt_state_canonical": 239,
            "changed_rows": edits,
            "deleted_states": [169],
            "boot_steps": tick,
            "boot_state_old": state,
            "boot_head": head,
            "one_count": len(ones),
            "one_positions": sorted(ones),
            "visited_head_range": visited,
            "dispatcher_visits_before_and_at_frame": q96_entries,
            "special_state_visits": special,
            "physical_registers": [0, 0, 0, 3, 0, 0, 3, 0, 0],
            "logical_registers": [3, 0, 0, 0, 3, 0, 0, 0, 0],
            "spare_values": [1] * 167,
            "marker_position": -6,
            "header_position": 176,
            "zero_exterior": True,
            "table_sha256": old_hash,
            "canonical_table_sha256": canonical_hash,
            "baseline_table_sha256": hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
            "supplied_table_matches_independent_reconstruction": supplied_match,
            "scope": "Exact finite blank bootstrap only; no inference from finite tests about unbounded runtime.",
        }
        reports.append(report)
        (args.output / f"boot_v{variant}.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({k: v for k, v in report.items() if k not in ("one_positions", "spare_values")}), flush=True)
    (args.output / "summary.json").write_text(json.dumps(reports, indent=2) + "\n")


if __name__ == "__main__":
    main()
