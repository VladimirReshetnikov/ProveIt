#!/usr/bin/env python3
"""Reproduce the scanner experiment, exact failure, and research summaries.

The default is deliberately small: two complete blank simulations, a separate
dense replay, a literal next-frame witness, and a universal symbolic witness.
The expensive searches and complete 8,391-case audit are opt-in.
"""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent
BASELINE_SHA256 = "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267"
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
INPUT_PC = "11101001001000000"
EXPECTED_PC = "1110100100100001"
WRONG_PC = "11101001001001"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        assert bit in ("0", "1") and write in ("0", "1")
        assert direction in ("L", "R")
        table[key] = int(write), (-1 if direction == "L" else 1), int(target)
    states = {q for q, _ in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for _, _, t in table.values()} - states == {254}
    return table


def paint(pc, distance, registers, spares, head=0):
    assert distance >= len(pc)
    ones = {head - 1, head + distance}
    ones.update(head + i for i, bit in enumerate(pc) if bit == "1")
    position = head + distance + 1
    for value in list(registers) + list(spares):
        assert type(value) is int and value >= 0
        ones.update(range(position + 1, position + value + 2))
        position += value + 2
    return ones


def sparse(table, steps, q=95, head=0, initial=(), watch=False):
    ones, used, failures, entries = set(initial), Counter(), [], 0
    for tick in range(steps):
        bit = int(head in ones)
        if watch and (q, bit) == (41, 0):
            entries += 1
            if head - 1 in ones or head - 2 in ones:
                failures.append(dict(tick=tick, head=head,
                                     leftward_bits=[int(head - j in ones) for j in range(3)]))
        used[q, bit] += 1
        write, direction, q = table[q, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    return q, head, ones, used, dict(entries=entries, failed_premises=failures)


def dense(table, steps):
    cells = bytearray(2 * steps + 3)
    origin = steps + 1
    position, q = origin, 95
    for _ in range(steps):
        write, direction, q = table[q, cells[position]]
        cells[position] = write
        position += direction
    return q, position - origin, {i - origin for i, bit in enumerate(cells) if bit}


def parse_complete(ones, head, max_path=51):
    """Recognize the whole normal tape, rejecting temporary dispatch visits."""
    if not ones or min(ones) != head - 1:
        return None
    possible_header = [p for p in ones if p >= head + max_path]
    if not possible_header:
        return None
    header = min(possible_header)
    if header - head < 64:
        return None
    raw = "".join(str(int(p in ones)) for p in range(head, header))
    pc = raw.rstrip("0")
    if len(pc) > max_path:
        return None
    values, position, maximum = [], header + 1, max(ones)
    while position <= maximum:
        if position in ones or position + 1 not in ones:
            return None
        first = position + 1
        position = first
        while position in ones:
            position += 1
        values.append(position - first - 1)
    if len(values) < 10:
        return None
    registers, spares = values[:9], values[9:]
    distance = header - head
    if paint(pc, distance, registers, spares, head) != ones:
        return None
    return dict(pc=pc, head=head, header_distance=distance,
                physical_registers=registers, spare_values=spares,
                all_one_positions=sorted(ones))


def first_complete(table):
    ones = paint(INPUT_PC, 64, [0] * 9, [1])
    q, head, dispatches = 96, 0, []
    for tick in range(1, 2001):
        write, direction, q = table[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
        if q == 96:
            frame = parse_complete(ones, head)
            dispatches.append(dict(step=tick, head=head, complete=frame is not None))
            if frame is not None:
                return dict(steps=tick, frame=frame, dispatch_visits=dispatches)
    raise AssertionError("No complete frame within the fixed diagnostic bound")


def local_contraction(table, altered):
    assert table[41, 0] == (0, -1, 58)
    assert table[58, 0] == (0, -1, 84)
    assert table[84, 0] == (0, 1, 84)
    assert altered[41, 0] == (0, -1, 84)
    # These three rows establish the rule for every exterior tape: all three
    # visited cells are required zero, and the rows leave them zero.
    return dict(status="PROVED_LOCAL_REWRITE", premise="At state 41 and head x, cells x,x-1,x-2 are zero",
                old_trace=[[41, 0], [58, -1], [84, -2], [84, -1]],
                new_trace=[[41, 0], [84, -1]],
                same_entire_tape=True, saved_literal_steps=2)


def structural_summaries():
    r = ROOT / "results"
    audit = json.loads((r / "scanner5-contract-audit.json").read_text())
    violations = audit["violations"]
    assert audit["cases"] == 8391
    assert audit["finite_run_scanner_entries"] == 99
    assert audit["unsafe_cases"] == audit["unsafe_local_entries"] == len(violations) == 99
    assert len({v["pc"] for v in violations}) == 50
    assert all(v["pc"].endswith("000000") and v["side"] == "L" and v["first_run"] == "1" for v in violations)
    assert Counter((v["op"], v["zero"]) for v in violations) == Counter({("CD", True): 49, ("CD", False): 49, ("CI", None): 1})
    mapping = json.loads((r / "scanner5-failure-grammar-map.json").read_text())
    assert {x["pc"] for x in mapping} == {v["pc"] for v in violations}
    one = json.loads((r / "one-action-summary.json").read_text())
    flexible = json.loads((r / "flexible-one-action-summary.json").read_text())
    context = json.loads((r / "context-action-summary.json").read_text())
    combined = [json.loads(line) for line in (r / "context-combination-summary.jsonl").read_text().splitlines()]
    assert one["deleted_states"] == 137 and one["candidates"] == 133712 and one["survivors"] == 0
    assert flexible["candidate_count"] == 133712 and flexible["survivors"] == 0
    assert context["rows"] == 467 and context["candidates"] == 455792
    assert context["individual_replacements"] == 762 and context["possible_eliminations"] == 13
    assert len((r / "context-action-options.txt").read_text().splitlines()) == 762
    assert all(x["cases"] == 8385 and x["finite_only"] for x in (one, flexible, context))
    assert len(combined) == 13 and all(x["found"] == 0 and x["finite_only"] for x in combined)
    assert {x["dead"] for x in combined if not x["complete"]} == {4, 30}
    assert all(x["literal_step_budget"] == 100000000 and x["branch_call_budget"] == 50000 for x in combined)
    return dict(status="FROZEN_SUMMARIES_INTERNALLY_CHECKED", universal_cases=8391,
                dangerous_cases=99, distinct_dangerous_paths=50,
                finite_search_fixtures=8385, one_action_recipes=133712,
                contextual_action_recipes=455792, individual_options=762,
                joint_state_domains=13, exhausted_joint_domains=11,
                budget_limited_states=[4, 30], finite_joint_survivors=0,
                note="Frozen summary checks do not rerun the full audit or searches; use the optional flags to reproduce them")


def run_search(reference, output):
    search = output / "search"
    search.mkdir(exist_ok=True)
    corpus = search / "candidate245-literal-cases.txt"
    archive = reference / "inputs/state_reduction/candidate245-literal-cases.txt.gz"
    with gzip.open(archive, "rb") as source, corpus.open("wb") as target:
        shutil.copyfileobj(source, target)
    programs = ["one_action_search", "resource_flexible_search", "context_action_search", "combine_context_actions"]
    for name in programs:
        binary = search / name
        subprocess.run(["g++", "-std=c++17", "-O3", str(ROOT / "code" / (name + ".cpp")), "-o", str(binary)], check=True)
        command = [str(binary), str(corpus)]
        if name == "combine_context_actions":
            command.append(str(search / "context-action-options.txt"))
        with (search / (name + ".log")).open("w") as log:
            subprocess.run(command, cwd=search, stdout=log, stderr=subprocess.STDOUT, check=True)
    for name in ("one-action-summary.json", "flexible-one-action-summary.json", "context-action-summary.json"):
        fresh = json.loads((search / name).read_text())
        frozen = json.loads((ROOT / "results" / name).read_text())
        fresh.pop("seconds", None)
        frozen.pop("seconds", None)
        assert fresh == frozen, name
    for name in ("context-action-options.txt", "context-combination-summary.jsonl"):
        assert (search / name).read_bytes() == (ROOT / "results" / name).read_bytes(), name
    return dict(status="REPRODUCED", output=str(search), finite_only=True)


def main():
    assert __debug__, "Do not run the verifier with Python optimization (-O)"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reference", required=True, type=Path, help="Extracted zfc245-proof-20261018 directory")
    ap.add_argument("--output", required=True, type=Path, help="Directory for fresh verification results")
    ap.add_argument("--full-scanner-audit", action="store_true")
    ap.add_argument("--search", action="store_true")
    args = ap.parse_args()
    reference, output = args.reference.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    baseline_path = reference / "certificate/machine_old.tm"
    experimental_path = ROOT / "machine/scanner5-experiment244-old.tm"
    assert digest(baseline_path) == BASELINE_SHA256
    baseline, experimental = read_table(baseline_path), read_table(experimental_path)
    assert len(baseline) == 490 and len(experimental) == 488
    sites = json.loads((reference / "certificate/sites_logical.json").read_text())
    assert len(sites) == 6460 and max(len(pc) for pc, _, _ in sites) == 51
    assert [INPUT_PC, "CD", 1] in sites
    allocation = json.loads((reference / "certificate/allocation.json").read_text())
    assert len(allocation) == 128 and len(set(allocation.values())) == 128
    reconstructed = {key: value for key, value in baseline.items() if key[0] != 58}
    reconstructed[41, 0] = (0, -1, 84)
    assert reconstructed == experimental
    assert all(row[2] != 58 for row in experimental.values())
    local = local_contraction(baseline, experimental)
    save(output / "local-contraction.json", local)
    bq, bh, bones, baseline_used, bwatch = sparse(baseline, 407915, watch=True)
    assert (bq, bh, bones) == (96, -5, paint("", 181, [0, 0, 0, 3, 0, 0, 3, 0, 0], [1] * 167, -5))
    assert bwatch == dict(entries=1411, failed_premises=[dict(tick=46732, head=0, leftward_bits=[0, 1, 1])])
    eq, eh, eones, used, _ = sparse(experimental, 818324)
    registers = [0, 1, 0, 4, 0, 0, 6, 0, 0]
    assert (eq, eh, eones) == (96, -8, paint("", 245, registers, [1] * 233, -8))
    assert dense(experimental, 818324) == (eq, eh, eones)
    assert len(eones) == 488
    boot = dict(status="EXACT_FINITE_BOOT_REPRODUCED", experimental_machine_status="UNVALIDATED_244_STATE_EXPERIMENT",
                steps=818324, state=eq, head=eh, marker=eh - 1, header=237,
                header_distance=245, pc="", physical_registers=registers,
                logical_registers=[registers[j] for j in PHYSICAL], spare_count=233,
                spare_values=[1] * 233, all_one_positions=sorted(eones), one_count=488,
                all_other_cells_zero=True, independent_dense_replay=True,
                used_rows=[[q, bit, count] for (q, bit), count in sorted(used.items())],
                baseline_steps=407915, baseline_local_premise_audit=bwatch)
    save(output / "scanner5-exact-boot.json", boot)
    rules = {word: (left, right) for word, left, right in json.loads((reference / "grammar.json").read_text())["rules"]}
    by_state = {state: word for word, state in allocation.items()}
    locks = [dict(word=by_state[q], bit=bit, target_word=rules[by_state[q]][bit],
                  occurrences=count, state=q)
             for (q, bit), count in sorted(used.items()) if q in by_state]
    assert len(locks) == 55
    assert locks == json.loads((ROOT / "results/scanner5-bootstrap-grammar-locks.json").read_text())
    assert {(q, bit) for q, bit in baseline_used if q in by_state} == {(q, bit) for q, bit in used if q in by_state}
    save(output / "scanner5-bootstrap-grammar-locks.json", locks)
    old_frame, new_frame = first_complete(baseline), first_complete(experimental)
    assert old_frame["steps"] == 574 and old_frame["frame"]["pc"] == EXPECTED_PC
    assert new_frame["steps"] == 650 and new_frame["frame"]["pc"] == WRONG_PC
    for result in (old_frame, new_frame):
        assert result["frame"]["head"] == 0 and result["frame"]["header_distance"] == 64
        assert result["frame"]["physical_registers"] == [0] * 9 and result["frame"]["spare_values"] == [1]
    witness = dict(status="REPRODUCED_WRONG_NEXT_COMPLETE_FRAME", input=dict(pc=INPUT_PC, head=0,
                   header_distance=64, physical_registers=[0] * 9, spare_values=[1],
                   all_one_positions=sorted(paint(INPUT_PC, 64, [0] * 9, [1]))), baseline=old_frame, experimental=new_frame)
    save(output / "scanner5-literal-wrong-successor.json", witness)
    spec = importlib.util.spec_from_file_location("framework_symbolic_wrong", ROOT / "code/symbolic_wrong_successor.py")
    symbolic = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(symbolic)
    universal = symbolic.run(reference, experimental_path)
    save(output / "scanner5-symbolic-wrong-successor.json", universal)
    summaries = structural_summaries()
    save(output / "frozen-summary-checks.json", summaries)
    map_spec = importlib.util.spec_from_file_location("framework_failure_map", ROOT / "code/map_scanner5_failures.py")
    mapper = importlib.util.module_from_spec(map_spec)
    map_spec.loader.exec_module(mapper)
    grammar_map = mapper.run(reference, ROOT / "results/scanner5-contract-audit.json")
    assert json.loads(json.dumps(grammar_map)) == json.loads((ROOT / "results/scanner5-failure-grammar-map.json").read_text())
    save(output / "scanner5-failure-grammar-map.json", grammar_map)
    result = dict(status="PASS_RESEARCH_VERIFICATION", valid_below245_solution=False,
                  baseline_table_sha256=digest(baseline_path), experimental_table_sha256=digest(experimental_path),
                  experimental_working_states=244, grammar_states=128, framework_states=116,
                  exact_boot_steps=818324, boot_word_read_pairs=55,
                  wrong_next_frame_universal_family=True,
                  full_audit_rerun=False, finite_searches_rerun=False)
    if args.full_scanner_audit:
        target = output / "scanner5-contract-audit.json"
        subprocess.run(["python3", str(ROOT / "code/scanner5_contract_audit.py"), "--reference", str(reference), "--output", str(target)], check=True)
        fresh = json.loads(target.read_text())
        frozen = json.loads((ROOT / "results/scanner5-contract-audit.json").read_text())
        fresh.pop("seconds", None)
        frozen.pop("seconds", None)
        assert fresh == frozen
        result["full_audit_rerun"] = True
    if args.search:
        result["search"] = run_search(reference, output)
        result["finite_searches_rerun"] = True
    save(output / "verification.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
