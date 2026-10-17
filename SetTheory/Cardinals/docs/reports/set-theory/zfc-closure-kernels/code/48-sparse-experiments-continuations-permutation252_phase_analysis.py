#!/usr/bin/env python3
"""Reproduce the finite zero-root phase analysis and its 503 focused folds.

Run with --output-prefix /tmp/name. The two outputs are name-analysis.json
and name-fold-search.json. The symbolic fuel is fixed at 1,000. No Lean,
Coq, blank-tape execution, candidate emission or larger search is performed.

The literal program is Mira-Cult's, verified by Jeff at upstream297ab8df7;
Wade supplied the compiler framework. The frozen252 table also uses
mira-emmy's public253 reduction at PR20 head0d544f2a. The symbolic diagnostic
comes from intake source27. Their original attribution/licensing is retained.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import re
import sys
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
import candidate252_independent_audit as audit

ROOT = Path(__file__).resolve().parent
BASE = Path(__file__).resolve().parent
FUEL = 1000
EXCLUDED = [8202, 8203, 8204, 8358, 8359, 8360]
PROG_SHA = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"
STRICT_SHA = "da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce"
CASE_MASKS_SHA = "2560c0d0d6ab69b39dff897a541d3621d612eeddcfed064d943300ea125b0cac"
OUTCOMES_SHA = "2cf953e4dc6113a88872afbfd3e8e84e64ec2ca98cdd4a2268bec9dc39b705a2"

# Historical independent read-only audit, embedded so reproduction needs no /tmp
# inputs. It transcribed RegisterPath with Bool lists and checked every edge.
INDEPENDENT_AUDIT = {
    "status": "PASS ordinary independent source/semantic audit; not a Lean proof",
    "source_sha256": "17f50451e4c59af7cda12c6d3f896bc34a574e8c4de77f7dc1e611c961de0f26",
    "result_sha256": "312ff5147644e5d56c944fe0a96070d79b4a36fe1784a79b9a39b1a59a4df7f3",
    "RegisterPath_sha256": "a1457f32034eb4da50c8755610a366805260aac711424bba8b516ccab4e5b879",
    "all_case_successors_compared": 8391,
    "inc_path_tests": 8191,
    "strip_path_tests": 10220,
    "feasible_nonhalt_postfix_edges": 8384,
    "findings": [
        "Increment retains carry zeros and same-length all-zero overflow.",
        "Consume pads/truncates to the exact leaf; all break/continue successors agree.",
        "Initial inclusion and every feasible abstract edge satisfy the postfix certificate.",
        "Two positive decrement guards and their four body instructions are excluded.",
    ],
    "limits": [
        "Starts at zeroRoot, not the older nonzero public253 register prefix.",
        "No kernel invariant, new bootstrap, weak bisimulation or machine claim.",
    ],
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def semantic_sha(value):
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def inc_path(path):
    """Exact RegisterPath.incPath: retain every cleared carry bit."""
    last = path.rfind("0")
    return (path[:last] + "1" + "0" * (len(path) - last - 1)
            if last >= 0 else "0" * len(path))


def strip_path(path, bit, count):
    while count and path:
        count -= path[-1] == bit
        path = path[:-1]
    return path


def successor(path, op, argument, zero):
    if op == "CI" or op == "CD" and not zero:
        return inc_path(path)
    if op == "CD":
        return inc_path(strip_path(path, "0", 1))
    if op == "CB":
        return inc_path(strip_path(path, "0", argument))
    if op == "CC":
        return strip_path(path, "1", argument)
    assert op == "CH"
    return None


def program_graph(raw):
    text = raw.decode().split("Definition p254_tab", 1)[1].split("[", 1)[1].split("].", 1)[0]
    edge = r"(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)"
    nodes = re.findall(r"\((" + edge + r"),\s*(" + edge + r")\)", text)
    assert len(nodes) == 6459
    sites, visited = [], []

    def visit(q, prefix):
        visited.append(q)
        for bit, edge_text in enumerate(nodes[q]):
            path = prefix + str(bit)
            op, *args = edge_text.split()
            argument = int(args[0]) if args else None
            if op == "CN":
                assert 0 <= argument < len(nodes)
                visit(argument, path)
            else:
                if op in ("CI", "CD"):
                    assert 0 <= argument < 9
                sites.append((path, op, argument))

    visit(0, "")
    assert len(visited) == len(set(visited)) == 6459 and len(sites) == 6460
    lookup = {path: i for i, (path, _, _) in enumerate(sites)}

    def decode(pc):
        q, path = 0, ""
        for _ in range(len(nodes) + 1):
            bit = pc[len(path)] if len(path) < len(pc) else "0"
            path += bit
            op, *args = nodes[q][int(bit)].split()
            if op == "CN":
                q = int(args[0])
            else:
                # These generated paths are clean; no physical1 is discarded.
                assert "1" not in pc[len(path):]
                return lookup[path]
        raise AssertionError("decoder fuel exhausted")

    cases, targets = [], []
    for site, (path, op, argument) in enumerate(sites):
        for zero in ((True, False) if op == "CD" else (None,)):
            cases.append((site, path, op, argument, zero))
            pc = successor(path, op, argument, zero)
            targets.append(None if pc is None else decode(pc))
    assert len(cases) == 8391
    return sites, cases, targets, decode("")


def inc_mask(mask):
    return (2 if mask & 1 else 0) | (4 if mask & 6 else 0)


def dec_mask(mask):
    return (1 if mask & 2 else 0) | (6 if mask & 4 else 0)


def transfer(values, case):
    _, _, op, register, zero = case
    result = list(values)
    if op == "CI":
        result[register] = inc_mask(result[register])
    elif op == "CD":
        if zero:
            if not result[register] & 1:
                return None
            result[register] = 1
        else:
            if not result[register] & 6:
                return None
            result[register] = dec_mask(result[register] & 6)
    return tuple(result)


def phase_analysis(sites, cases, targets, first):
    by_site = defaultdict(list)
    for index, case in enumerate(cases):
        by_site[case[0]].append(index)
    values = [None] * len(sites)
    values[first] = (1,) * 9
    pending, pops = deque([first]), 0
    while pending:
        site = pending.popleft()
        pops += 1
        for index in by_site[site]:
            target = targets[index]
            if target is None:
                continue
            result = transfer(values[site], cases[index])
            if result is None:
                continue
            old = values[target]
            joined = result if old is None else tuple(a | b for a, b in zip(old, result))
            if old != joined:
                values[target] = joined
                pending.append(target)

    # Check the final certificate directly, without relying on worklist order.
    assert first == 0 and all(mask & 1 for mask in values[first])
    enabled, postfix_edges = [], 0
    for case, target in zip(cases, targets):
        old = values[case[0]]
        result = None if old is None else transfer(old, case)
        enabled.append(result is not None)
        if result is not None and target is not None:
            assert values[target] is not None
            assert all(a & ~b == 0 for a, b in zip(result, values[target]))
            postfix_edges += 1
    assert [i for i, yes in enumerate(enabled) if not yes] == EXCLUDED
    assert sum(v is not None for v in values) == 6456 and sum(enabled) == 8385
    assert postfix_edges == 8384 and pops == 37238
    return values, enabled, pops, postfix_edges


def case_json(index, cases, values, enabled):
    site, path, op, argument, zero = cases[index]
    masks = values[site]
    return dict(index=index, path=path, op=op, logical_register=argument,
                zero=zero, possible=enabled[index], masks=None if masks is None else list(masks))


class Tracking(dict):
    def __init__(self, rows):
        super().__init__(rows)
        self.used = set()

    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def load_strict(path):
    sys.dont_write_bytecode = True
    sys.modules["cost_search"] = SimpleNamespace()
    spec = importlib.util.spec_from_file_location("permutation252_phase_strict", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def focused_screen(table, states, protected, cases, case_rows, enabled, recipes, strict):
    symbolic = []
    for _, path, op, argument, zero in cases:
        physical = audit.NEWPHYS[argument] if op in ("CI", "CD") else argument
        guard = (physical, zero) if op == "CD" else None
        # This helper deliberately normalizes physical PC carry zeros. Its
        # overflow case uses gap41; it is NOT the exact RM graph successor.
        pc = audit.successor(path, op, argument, zero)
        effect = (("inc", physical) if op == "CI" else
                  ("dec", physical) if op == "CD" and not zero else None)
        right = ([('b', int(bit)) for bit in pc] if pc is not None else [])
        right += [('r', 0, 1, (41 if pc is None else 40) - len(pc or "")),
                  ('b', 1), ('box', ('plain', effect))]
        symbolic.append((path, op, guard, strict.canon([('b', 1)], right)))

    def check(rows, index):
        path, op, guard, target = symbolic[index]
        try:
            rules, literal = strict.run(rows, path, guard, target, halt=op == "CH", fuel=FUEL)
            assert literal > 0
            return True, None, None, sum(rules.values())
        except AssertionError as error:
            reason = str(error)
            kind = "fuel" if reason == "symbolic fuel exhausted" else "unsupported_symbolic_rule"
            return False, reason, kind, None
        except KeyError as error:
            return False, str(error), "missing_row", None

    allowed = [i for i, yes in enumerate(enabled) if yes]
    used, weights = {}, {}
    for index in allowed:
        traced = Tracking(table)
        ok, reason, _, weight = check(traced, index)
        assert ok, ("baseline", index, reason)
        used[index], weights[index] = traced.used, weight
    groups = {}
    for deleted in sorted({r['deleted'] for r in recipes}):
        dead = str(deleted)
        affected = {key for key, (_, _, target) in table.items() if key[0] == dead or target == dead}
        groups[deleted] = sorted((i for i in allowed if used[i] & affected),
                                 key=lambda i: (weights[i], i))
    records, survivors, checks = [], [], 0
    for recipe in recipes:
        dead, replacement = str(recipe['deleted']), str(recipe['target'])
        current = {key: (write, direction, replacement if target == dead else target)
                   for key, (write, direction, target) in table.items() if key[0] != dead}
        assert len(current) == 502 and len({q for q, _ in current}) == 251
        assert all(current[key] == table[key] for key in protected)
        assert all(current['64', bit] == table['64', bit] for bit in (0, 1))
        assert all(target == '254' or (target, 0) in current for _, _, target in current.values())
        checked, failure = 0, None
        for index in groups[int(dead)]:
            ok, reason, kind, _ = check(current, index)
            checked += 1
            if not ok:
                failure = dict(case=case_rows[index], reason=reason, rejection_kind=kind)
                break
        if failure is None:
            # Prefilter survivors always receive every one of the8385 guards.
            for index in allowed:
                ok, reason, kind, _ = check(current, index)
                checked += 1
                if not ok:
                    failure = dict(case=case_rows[index], reason=reason, rejection_kind=kind)
                    break
        record = dict(deleted=int(dead), target=int(replacement),
                      old_excluded_first_failure=recipe['first_failure']['index'],
                      candidate_checks=checked,
                      status="checker_rejected" if failure else "passed_all_8385_checks",
                      first_failure=failure)
        checks += checked
        records.append(record)
        if failure is None:
            survivors.append(record)
    normalized = [dict(deleted=r['deleted'], target=r['target'],
                       old_excluded_first_failure=r['old_excluded_first_failure'],
                       candidate_checks=r['candidate_checks'],
                       first_failure_case_index=r['first_failure']['case']['index'] if r['first_failure'] else None,
                       first_failure_reason=r['first_failure']['reason'] if r['first_failure'] else None)
                  for r in records]
    assert len(records) == 503 and checks == 519 and not survivors
    assert semantic_sha(normalized) == OUTCOMES_SHA
    return dict(status="completed", planned_recipes=503, completed=503,
                baseline_passed=8385, candidate_checks=checks, recipes=records,
                survivors=survivors, historical_outcomes_sha256=OUTCOMES_SHA,
                historical_503_recipe_outcomes_exact=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-prefix", type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Run without -O; the inherited checker uses assertions")
    prefix = args.output_prefix.resolve()
    if prefix == Path('/') or prefix == ROOT or ROOT in prefix.parents:
        parser.error("output-prefix must be outside the checkout")
    began = time.monotonic()
    prog = ROOT / "lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v"
    frozen = BASE / "candidate-permutation252/zfc_permutation252_old.tm"
    fold_file = BASE / "results/permutation252-fold-search.json"
    strict_file = ROOT / "SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py"
    prog_raw, raw = prog.read_bytes(), frozen.read_bytes()
    assert sha(prog_raw) == PROG_SHA and sha(raw) == audit.EXPECTED_SHA
    assert sha(strict_file.read_bytes()) == STRICT_SHA
    assert tuple(audit.NEWPHYS) == (6, 2, 0, 4, 3, 7, 8, 5, 1)
    numeric = audit.read_table(raw)
    table = {(str(q), bit): (write, direction, str(target))
             for (q, bit), (write, direction, target) in numeric.items()}
    states = sorted({q for q, _ in table}, key=int)
    protected = {(str(q), bit) for q, bit in audit.BOX_PAIRS}
    assert len(table) == 504 and len(states) == 252 and len(protected) == 55
    sites, cases, targets, first = program_graph(prog_raw)
    values, enabled, pops, postfix_edges = phase_analysis(sites, cases, targets, first)
    rows = [case_json(i, cases, values, enabled) for i in range(len(cases))]
    assert semantic_sha(rows) == CASE_MASKS_SHA
    classes = [None] + sorted({v for v in values if v is not None})
    assert len(classes) == 121
    class_id = {value: i for i, value in enumerate(classes)}
    fold = json.loads(fold_file.read_text())
    assert fold['table_sha256'] == audit.EXPECTED_SHA
    assert fold['working_states_old'] == list(map(int, states))
    recipes = []
    for group in fold['sources']:
        destinations = [s for s in states if int(s) != group['deleted_old']]
        failures = group['first_failure_case_in_destination_order']
        assert len(destinations) == len(failures)
        for target, index in zip(destinations, failures):
            if index is not None and not enabled[index]:
                recipes.append(dict(deleted=group['deleted_old'], target=int(target), first_failure=rows[index]))
    assert len(recipes) == 503
    common = dict(driver_sha256=sha(Path(__file__).read_bytes()),
                  python=platform.python_version(), command=[sys.executable, *sys.argv],
                  upstream_commit="297ab8df7e5de329605c3875b4934643b371a5e3",
                  public253_PR20_head="0d544f2a2e3c18f12278441a74b7879f31cbe856",
                  attribution="Mira-Cult program; Jeff verification; Wade framework; mira-emmy public253; intake source27 symbolic diagnostic; independent permutation252.",
                  sources={str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in
                           [prog, frozen, fold_file, strict_file, Path(audit.__file__)]},
                  logical_to_physical=list(audit.NEWPHYS))
    analysis = dict(common, status="PASS ordinary phase analysis and postfix certificate",
                    scope="Cartesian0/1/>=2 masks from literal zeroRoot only. No Lean invariant or changed-machine claim.",
                    literal_nodes=6459, sites=6460, guards=8391, initial_site=first,
                    reachable_sites_overapprox=6456, reachable_guards_overapprox=8385,
                    unreachable_guards=6, worklist_pops=pops,
                    mask_classes=[None if v is None else list(v) for v in classes],
                    site_mask_class_ids=[class_id[v] for v in values],
                    mask_class_count=len(classes), mask_bits={"1": "0", "2": "1", "4": ">=2"},
                    excluded_guards=[rows[i] for i in EXCLUDED],
                    postfix_check=dict(initial_zero_tuple_included=True, all_feasible_edges_closed=True,
                                       feasible_nonhalt_edges=postfix_edges),
                    expanded_case_masks_sha256=CASE_MASKS_SHA,
                    selected_recipes=[[r['deleted'], r['target'], r['first_failure']['index']] for r in recipes],
                    historical_independent_audit=INDEPENDENT_AUDIT)
    search = focused_screen(table, states, protected, cases, rows, enabled, recipes, load_strict(strict_file))
    search.update(common)
    search.update(scope="Bounded focused251-state symbolic screen, excluding only six source-program guards. Checker rejection is not a mathematical counterexample or impossibility result; no blank-start or consistency claim.",
                  guards_required=8385, excluded_guards=[rows[i] for i in EXCLUDED],
                  protected_rows=55, unchanged_start_old=64, working_count=251,
                  candidate_transition_rows=502, fuel=FUEL,
                  rejection_histogram=dict(Counter(r['first_failure']['rejection_kind'] for r in search['recipes'])),
                  expected_physical_target_convention="candidate252_independent_audit.successor; normalized carry with overflow gap41, distinct from exact RM incPath graph.",
                  argument_field_note="logical_register is a register for CI/CD; for CB/CC it is the control-pop count.",
                  finite_rejection_is_not_impossibility=True)
    analysis['elapsed_seconds'] = time.monotonic() - began
    search['elapsed_seconds'] = analysis['elapsed_seconds']
    prefix.parent.mkdir(parents=True, exist_ok=True)
    paths = [Path(str(prefix) + "-analysis.json"), Path(str(prefix) + "-fold-search.json")]
    for path, result in zip(paths, [analysis, search]):
        path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", outputs=list(map(str, paths)),
                          mask_classes=121, possible_leaves=6456, possible_guards=8385,
                          recipes=503, candidate_checks=519, survivors=0,
                          elapsed_seconds=search['elapsed_seconds']), indent=2))


if __name__ == "__main__":
    main()
