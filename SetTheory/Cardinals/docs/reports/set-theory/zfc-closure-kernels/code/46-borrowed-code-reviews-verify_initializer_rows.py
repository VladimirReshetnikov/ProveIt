"""Independent finite checks for the eight selected initializer controls.

Uses only the Python standard library. It imports neither the constructor,
the quotient implementation, nor the simulator. It checks exact literal
row equations and independently derived closed-form endpoint coordinates;
it does not rerun the affine runtime checks or establish Con(ZFC).
"""
from pathlib import Path
import argparse
import hashlib
import json


def read_table(path):
    data = path.read_bytes()
    lines = data.decode("ascii").splitlines()
    assert lines[0] == "#! start 0"
    rows = {}
    for line in lines[1:]:
        q, read, write, move, dest = line.split()
        q, read, write, dest = map(int, (q, read, write, dest))
        assert (q, read) not in rows
        assert read in (0, 1) and write in (0, 1) and move in ("L", "R")
        rows[q, read] = (write, move, dest)
    count = len(rows) // 2
    assert set(rows) == {(q, b) for q in range(count) for b in (0, 1)}
    assert all(0 <= action[2] <= count for action in rows.values())
    return rows, count, hashlib.sha256(data).hexdigest()


def check_record(machine_folder, certificate_folder, record):
    source, n, digest_s = read_table(machine_folder / record["raw_table"])
    target, m, digest_t = read_table(machine_folder / record["quotient_table"])
    cert = json.loads((certificate_folder / record["quotient_certificate"]).read_text())
    h = cert["state_map"]
    assert len(h) == n + 1
    assert all(type(q) is int for q in h)
    assert h[0] == 0 and h[n] == m
    assert set(h[:-1]) == set(range(m))
    assert n == cert["source_states"] == record["raw_states"]
    assert m == cert["target_states"] == record["quotient_states"]
    assert digest_s == record["raw_sha256"]
    assert digest_t == record["quotient_sha256"]
    for q in range(n):
        for b in (0, 1):
            w, d, r = source[q, b]
            assert target[h[q], b] == (w, d, h[r])
    classes = [[q for q in range(n) if h[q] == r] for r in range(m)]
    assert [g for g in classes if len(g) > 1] == cert["nontrivial_classes"]
    assert h[record["raw_root_state"]] == record["quotient_root_state"]
    # Label identities are source metadata; the semantic check above uses
    # only the numeric state map and literal rows.
    assert record["quotient_classes"] == [["b:1", "e:5"]]

    # Coordinates follow from the whole-tape invariant, without simulation.
    c = record["initializer"]
    width = c["counter_bits"]
    assert type(width) is int and width >= 9 and c["shared_exit"] is True
    one_sentinel = c["kind"] == "registers_one_sentinel"
    assert one_sentinel or c["kind"] == "registers"
    np = c["initial_registers"][0]
    assert c["initial_registers"] == [0 if one_sentinel else 2] + [0] * 8
    assert c["physical_order"] == [2, 4, 3, 7, 6, 8, 0, 1, 5]
    assert c["spare_registers"] == [0] * (width - 9)
    assert c["successful_decrements"] == 2 ** width - 1
    assert c["seed_steps"] == 2 * width + (5 if one_sentinel else 6)
    seed_left = -2 * width - (4 if one_sentinel else 5)
    marker = seed_left - (2 ** width - 1)
    delimiter = seed_left + 3
    ones = {marker, delimiter}
    ones.update(seed_left + 5 + 2 * j for j in range(width))
    if np == 2:
        ones.add(seed_left + 18)             # separator of old block 7
        ones.add(seed_left + 2 * width + 5)  # retained right terminal bit
    steps = 4 ** width + 14 * 2 ** width + 2 * width
    steps += 18 if one_sentinel else 19     # standalone constant + shared 20
    run = record["blank_run"]
    assert run["head"] == marker + 1
    assert run["final_ones"] == sorted(ones)
    assert run["steps"] == c["blank_steps"] == steps
    assert c["gap"] == 2 ** width + 1 == delimiter - marker - 1
    assert c["initializer_states"] == 2 * width + (13 if one_sentinel else 14)
    data = json.dumps(dict(head=marker + 1, ones=sorted(ones)),
                      sort_keys=True, separators=(",", ":")).encode()
    assert hashlib.sha256(data).hexdigest() == run["whole_tape_sha256"]
    return dict(table=record["quotient_table"], raw_states=n,
                quotient_states=m, row_equations=2 * n,
                table_sha256=digest_t, endpoint_head=marker + 1,
                endpoint_ones=len(ones), blank_steps=steps,
                exact_row_equations_pass=True,
                analytic_endpoint_matches_record=True,
                simulation_reexecuted=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2],
                        help="artifact package root (default: locate from this script)")
    parser.add_argument("--output", type=Path,
                        help="also save JSON to this path; default is stdout only")
    args = parser.parse_args()
    root = args.root.resolve()
    certificate_folder = root / "data" / "initializer"
    machine_folder = root / "machines" / "initializer"
    summary = json.loads((certificate_folder / "final_controls_summary.json").read_text())
    records = summary["records"]
    assert len(records) == 8
    assert len({r["quotient_table"] for r in records}) == len(records)
    results = [check_record(machine_folder, certificate_folder, r) for r in records]
    result = dict(selected_controls_checked=len(results),
                  row_equations_checked=sum(r["row_equations"] for r in results),
                  imported_constructor_or_simulator=False,
                  kernel_checked=False, new_consistency_bound_claimed=False,
                  results=results)
    output = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled; Python -O is unsupported")
    main()
