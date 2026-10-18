#!/usr/bin/env python3
"""Measure register-sharing obstacles and matched 2-adic codec replacements.

The complete original nine logical rows, CP/GIC/native-equality bundle, gates,
MP/DROP/NIP and exhaustive-candidate shell remain present.  The eight-register
variant changes *all* pair representations to E(a,b)=2**a*(2*b+1)-1; it is not
an allocation of the unchanged numeric program.  Hybrid variants retain the
Cantor formula codec and nine registers.  These are compiler experiments, not
new verified consistency machines.  No Lean or submitted build tool is run.

The pinned public Wade backend is copied to external scratch before execution.
Its generic bootstrap is charged in full but its new startup invariant is not
proved here.  Generated tables, source DAGs and labels remain outside Git.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import copy
import hashlib
import importlib
import json
from pathlib import Path
import platform
import sys
import time

import recover_wade_dag as recover
from full_grammar_experiment import expand, load_file, normalize, safe_repair
from pairing_backend_experiment import execute_helper
import theory_backend_experiment as theory

ROOT = Path(__file__).resolve().parents[4]
REPORT = ROOT / "SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels"


def E(a, b):
    return (1 << a) * (2 * b + 1) - 1


def unE(n):
    n += 1
    a = 0
    while n % 2 == 0:
        a += 1
        n //= 2
    return a, n // 2


def macro_word(builder, root, boundary):
    if root in boundary:
        return [root]
    if not isinstance(root, int):
        raise ValueError("AX escaped its declared closed macro boundary")
    return [v for child in builder.sequences[root].seq
            for v in macro_word(builder, child, boundary)]


def liveness(nodes):
    """Exact finite CFG, deliberately conservative use/def interpretation.

    INC is read-modify-write, not a kill.  DECNZ reads its input on both
    branches.  This calculation does NOT know that a destructive loop clears
    a register.  The separate exact unpair witness supplies the sharper local
    obstruction; a nine-clique in this overapproximation is not a lower bound.
    """
    source = REPORT / "code/08-schema-machine-rebracket_axioms.py"
    helper = load_file("register_lifetime_source08", source)
    machine = helper.PathMachine(nodes)
    first = machine.normalize(())
    pending, seen, successors = deque([first]), {first}, {}
    while pending:
        q = pending.popleft()
        successors[q] = machine.successors(*q)
        for s in successors[q]:
            if s not in seen:
                seen.add(s)
                pending.append(s)
    predecessors = defaultdict(set)
    for q, children in successors.items():
        for s in children:
            predecessors[s].add(q)
    live = {q: set() for q in seen}
    for r in range(9):
        uses = {q for q in seen if q[1] in (f"EInc {r}", f"EDecnz {r}")}
        queue = deque(uses)
        while queue:
            q = queue.popleft()
            if r in live[q]:
                continue
            live[q].add(r)
            queue.extend(predecessors[q])
    # An exact legal input to the *checked macro contract*, not a blank-reachability claim.
    x = y = 0
    for _ in range(100):
        x, y = (y + 1, 0) if x == 0 else (x - 1, y + 1)
    registers = [101, 103, 107, 109, 113, 127, x, y, 900]
    assert (x, y) == (4, 9) and len(set(registers)) == 9
    cantor = lambda a, b: (a + b) * (a + b + 1) // 2 + b
    assert cantor(x, y) + registers[8] == 1000
    dependencies = [cantor(x + 1, y) + 900,
                    cantor(x, y + 1) + 900,
                    cantor(x, y) + 901]
    assert all(v != 1000 for v in dependencies)
    return dict(unfolded_sites=machine.site_count,
                normalized_reachable_sites=len(seen), max_path_depth=machine.max_depth,
                instruction_histogram=dict(Counter(q[1].split()[0] for q in seen)),
                conservative_live_histogram=dict(Counter(map(len, live.values()))),
                conservative_analysis_has_no_clear_loop_summaries=True,
                original_unpair_macro_witness=dict(initial=[101, 103, 107, 109, 113, 127, 0, 0, 1000],
                    after_iterations=100, registers=registers, remaining_encoded_value=1000,
                    x_y_l_perturbations_change_result=dependencies,
                    blank_or_safe_invariant_reachability_claimed=False),
                register_lower_bound_claimed=False)


def make_variant(backend, nodes, names, mode):
    b = recover.builder_from_dag(backend, nodes, names)
    b.sequence_lookup = {s.seq: i for i, s in enumerate(b.sequences)}
    regs = [b.reg(n) for n in recover.REGISTERS]
    word_adic = mode in ("all-eight", "word-only", "word-stack")
    stack_adic = mode in ("all-eight", "stack-only", "word-stack")

    def seq(items, name):
        q = b.add_sequence(items)
        if isinstance(q, int) and b.sequences[q].name is None:
            b.sequences[q].name = name + "().0"
        return q

    def raw(items):
        return items[0] if len(items) == 1 else [items[0], raw(items[1:])]

    def move(i, j):
        return b.while_decnz(regs[i], regs[j].inc)

    def clear(i):
        return b.while_decnz(regs[i], ())

    def scale(i, k):
        return seq([b.while_decnz(regs[i], [regs[6].inc] * k), move(6, i)], f"scale{i}x{k}")

    def extract(src, body, name, scratch=6):
        # Increment enc->enc+1; each even half restores source and clears scratch
        # BEFORE body.  At the final odd half, scratch holds tail, source is zero.
        odd = b.label("test", [[regs[src].decnz, "break_test"], "break_outer"])
        half = b.label("halve", [regs[src].decnz,
                    [odd, [regs[scratch].inc, "continue_halve"]]])
        outer = b.label("outer", [half,
                    raw([move(scratch, src), body, "continue_outer"])])
        return seq([regs[src].inc, outer, move(scratch, src)], name)

    roots = {}
    if stack_adic:
        push = seq([scale(2, 2), regs[2].inc,
                    b.while_decnz(regs[1], scale(2, 2)), regs[2].decnz], "push2adic")
        roots["push"] = push
        b.sequences[171].seq = b.sequences[push].seq
        pop = extract(2, regs[5].inc, "popH2adic")
        roots["popH"] = pop
        b.sequences[170].seq = b.sequences[pop].seq
        if mode == "all-eight":
            cons = seq([scale(1, 2), regs[1].inc,
                        extract(2, scale(1, 2), "factor_stack"),
                        regs[1].decnz, scale(1, 4)], "cons2adic")
        else:
            cons = seq([extract(2, regs[6].inc, "stack_head", scratch=7),
                        162, 117], "consCantorFrom2adicStack")
        roots["cons"] = cons
        b.sequences[119].seq = b.sequences[cons].seq
    if word_adic:
        for dst in (1, 3, 4, 5):
            roots[f"read{dst}"] = extract(8, regs[dst].inc, f"read2adic{dst}")
        for old, dst in ((174, 3), (175, 4), (176, 5)):
            b.sequences[old].seq = b.sequences[roots[f"read{dst}"]].seq
        # Old node35's read158;move208 is one additive read into T.
        b.sequences[35].seq = roots["read1"], 58
    if mode == "all-eight":
        # Preserve A; use X to count matched decrements; destroy H.
        match = b.label("walk", [regs[3].decnz,
                    [[regs[5].decnz, [regs[6].inc, "continue_walk"]],
                     [regs[3].inc, "break_cmp"]]])
        compare = b.label("cmp", [match,
                    [[regs[5].decnz, [clear(5), "break_cmp"]], clear(1)]])
        cmp = seq([compare, move(6, 3)], "preserve_compare")
        roots["compare"] = cmp
        roots["clearA"] = seq(clear(3), "clearA")
        gate = seq([cmp, 197, cmp, roots["clearA"]], "gates2adic")
        b.sequences[71].seq = b.sequences[gate].seq
    b.reduce_to_cons()
    b.name_sequences()
    old_word, _, contract = theory.old_contract(nodes)
    new_word, inverse_word, i = [], [], 0
    stop = len(old_word) - 5 if mode == "all-eight" else len(old_word)
    while i < stop:
        if word_adic and old_word[i:i + 2] == [158, 208]:
            new_word.append(roots["read1"])
            inverse_word.extend([158, 208])
            i += 2
        else:
            new_word.append(old_word[i])
            inverse_word.append(old_word[i])
            i += 1
    if mode == "all-eight":
        new_word += [roots["compare"], 197, roots["compare"], roots["clearA"]]
        inverse_word += theory.TAIL
    assert inverse_word == old_word
    boundary = set(theory.MACROS) | {roots[key] for key in ("read1", "compare", "clearA") if key in roots}
    assert macro_word(b, 1, boundary) == new_word
    contract.update(new_word_inverse_is_original_full_word=True,
                    actual_modified_AX_expands_to_checked_macro_word=True,
                    equality_is_symbolic_under_changed_pairing_not_old_numeric_codes=True)
    return b, roots, new_word, contract


def finite_checks(builder, roots, mode):
    count = Counter()
    cantor = lambda a, z: (a + z) * (a + z + 1) // 2 + z
    def un_cantor(n):
        a = b = 0
        for _ in range(n):
            a, b = (b + 1, 0) if a == 0 else (a - 1, b + 1)
        return a, b

    def check(root, values, expected, family):
        before = values[:]
        out = execute_helper(builder, root, values, fuel=10_000_000)
        if out != ("normal",) or values != expected:
            raise ValueError((family, before, out, values, expected))
        count[family] += 1

    for a in range(6):
        for t in range(6):
            assert unE(E(a, t)) == (a, t)
            if "push" in roots:
                v = [11, a, t, 13, 17, 19, 0, 0, 23]
                w = v[:]; w[1] = 0; w[2] = E(a, t)
                check(171, v, w, "push")
                for rest in (0, 1, 3):
                    v = [11, t, E(a, rest), 13, 17, 19, 0, 0, 23]
                    w = v[:]; w[1] = 4 * (E if mode == "all-eight" else cantor)(a, t); w[2] = rest
                    check(119, v, w, "cons")
                v = [11, 13, E(a, t), 19, 23, 29, 0, 0, 31]
                w = v[:]; w[2] = t; w[5] += a
                check(170, v, w, "popH")
            for dst in (1, 3, 4, 5):
                if f"read{dst}" in roots:
                    v = [11, 13, 17, 19, 23, 29, 0, 0, E(a, t)]
                    w = v[:]; w[dst] += a; w[8] = t
                    check(roots[f"read{dst}"], v, w, "additive_read")
    if mode == "all-eight":
        for a in range(9):
            for h in range(9):
                v = [11, 13, 17, a, 19, h, 0, 0, 23]
                w = v[:]; w[5] = 0; w[1] = 0 if a == h else 13
                check(roots["compare"], v, w, "preserving_compare")
        for a in range(7):
            for h in range(7):
                for d in range(7):
                    v = [11, 13, 17, a, d, h, 0, 0, 23]
                    w = v[:]; w[3] = w[4] = w[5] = 0
                    w[1] = 0 if a in (d, h) else 13
                    check(71, v, w, "both_freshness_gates")
    word_pair = E if mode in ("all-eight", "word-only", "word-stack") else cantor
    stack_pair = E if mode in ("all-eight", "stack-only", "word-stack") else cantor
    stack_unpair = unE if stack_pair is E else un_cantor
    formula_pair = E if mode == "all-eight" else cantor
    # Independent one-command spec for the unchanged three non-AX branches.
    # AX's enormous new integers are covered by symbolic full-row preservation,
    # NOT by approximate integer hashes or by this finite numeric test family.
    for opcode in (0, 1, 2):
        for top in range(3):
            for d in range(2):
                for delta in range(2):
                    premise = 4 * formula_pair(top, d + delta)
                    for h in sorted({0, 1, 2, premise}):
                        ws, tail = stack_pair(2, 1), 2
                        pl = 1 + word_pair(opcode, word_pair(delta, tail))
                        v = [7, top, ws, 0, d, h, 0, 0, pl]
                        w = v[:]; w[4] += delta; w[8] = tail
                        if opcode == 2 and h == 1:
                            assert execute_helper(builder, 0, v) == ("halt",)
                            count["NIP_false_halt"] += 1
                            continue
                        if opcode == 0:
                            w[1] = w[4] if premise == h else 0
                            w[2] = stack_pair(0, ws) if premise == h else ws
                            w[5] = 0
                        elif opcode == 1:
                            w[1], w[2] = h, stack_pair(top, ws)
                        else:
                            w[5], w[2] = stack_unpair(ws)
                        check(0, v, w, "main_MP_DROP_NIP")
    for pl in range(9):
        v = [7, 11, 13, 17, 19, 23, 0, 0, pl]
        w = v[:]
        w[0], w[8] = (8, 7) if pl == 0 else (7, pl - 1)
        check(133, v, w, "fetch_scheduler")
    return dict(count)


def compile_measure(backend, builder, mode, destination):
    live = set(builder.reachable())
    if mode == "all-eight":
        assert not any("scratch2" in str(e) for q in live for e in builder.sequences[q].seq)
    c = backend.TMBuilder()
    declarations = [n for n in recover.REGISTERS if mode != "all-eight" or n != "scratch2"]
    for name in declarations:
        c.reg(name)
    c.sequences = copy.deepcopy(builder.sequences)
    c.generate(); c.tm.gc()
    ids = {name: i for i, name in enumerate(recover.REGISTERS)}

    def edge(value):
        if isinstance(value, int): return f"ENode {value}"
        if value == "halt": return "EHalt"
        if value.startswith("_break."): return "EBreak " + value.split(".")[1]
        if value.startswith("_continue."): return "EContinue " + value.split(".")[1]
        _, name, kind = value.split(".")
        return ("EInc " if kind == "inc" else "EDecnz ") + str(ids[name])

    nodes = {q: tuple(map(edge, c.sequences[q].seq)) for q in live}
    names = {q: c.sequences[q].name for q in live}
    assert len(set(names.values())) == len(live)
    recover.reextract(c.tm, nodes, names)
    working = {q for q, _ in c.tm.states}
    framework = {q for q in working if q[0].isdigit()}
    result = dict(total_states=len(working), decision_states=len(working - framework),
                  framework_states=len(framework), physical_declarations=declarations,
                  every_decision_edge_reextracted=True, generic_Wade_bootstrap_included=True,
                  blank_startup_invariant_proved=False, logical_register_ids_keep_old_names=True)
    if destination is not None:
        destination.mkdir(exist_ok=True)
        data, labels, missing = normalize(c.tm)
        (destination / "machine.tm").write_bytes(data)
        (destination / "labels.json").write_text(json.dumps(labels, indent=2) + "\n")
        (destination / "dag.json").write_text(json.dumps(dict(root=0, nodes=nodes, names=names), indent=2) + "\n")
        result.update(machine_sha256=hashlib.sha256(data).hexdigest(),
                      transition_rows=len(data.splitlines()) - 1,
                      missing_rows_totalized_to_halt=missing,
                      missing_row_unreachability_proved=False)
    return result


def main():
    if not __debug__:
        raise RuntimeError("Run without -O; inherited checks use assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seeds", type=int, default=32)
    args = parser.parse_args()
    work = args.scratch.resolve()
    if work == ROOT or ROOT in work.parents or work == Path("/"):
        parser.error("scratch must be outside the checkout")
    if not 1 <= args.seeds <= 64:
        parser.error("bounded probe requires 1..64 seeds")
    work.mkdir(parents=True, exist_ok=True)
    backend_dir = work / "backend"; backend_dir.mkdir(exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (backend_dir / name).write_bytes(recover.git_bytes(None, "ZF/generator/" + name))
    sys.path.insert(0, str(backend_dir))
    backend = importlib.import_module("TMBuilder")
    raw = recover.git_bytes(None, "ZF/m254/coq/prog/Dag254.v")
    nodes, names = recover.parse_dag(raw.decode())
    start = time.monotonic()
    results = {}
    baseline = recover.builder_from_dag(backend, nodes, names)
    results["original-nine"] = dict(unshared=compile_measure(backend, baseline, "original-nine", work / "original-nine"))
    for mode in ("all-eight", "word-only", "stack-only", "word-stack"):
        builder, roots, word, contract = make_variant(backend, nodes, names, mode)
        checks = finite_checks(builder, roots, mode)
        unshared = compile_measure(backend, builder, mode, work / (mode + "-unshared"))
        base = copy.deepcopy(builder)
        # Re-Pair reserves token300+i.  New macro node IDs may themselves exceed
        # 300, so use a disjoint compact terminal alphabet before invoking it.
        vocabulary = sorted(set(word))
        assert len(vocabulary) < 300
        terminal = {value: i for i, value in enumerate(vocabulary)}
        compact_word = [terminal[value] for value in word]
        boundary = set(theory.MACROS) | set(vocabulary)
        histogram, candidates, best_key, best_builder = Counter(), [], None, None
        for seed in range(args.seeds):
            builder = copy.deepcopy(base)
            residual, productions, _ = safe_repair(compact_word, seed, 2)
            assert expand(residual, productions) == compact_word
            ids = {}
            def token(value):
                return ids[value] if value >= 300 else vocabulary[value]
            for i, pair in enumerate(productions):
                ids[300 + i] = builder.add_sequence([token(v) for v in pair])
            root = builder.add_sequence([token(v) for v in residual])
            builder.sequences[1].seq = builder.sequences[root].seq
            builder.reduce_to_cons(); builder.name_sequences()
            assert macro_word(builder, 1, boundary) == word
            result = compile_measure(backend, builder, mode, None)
            result["seed"] = seed
            candidates.append(result)
            histogram[result["total_states"]] += 1
            key = result["total_states"], result["decision_states"], seed
            if best_key is None or key < best_key:
                best_key, best_builder = key, builder
        best = compile_measure(backend, best_builder, mode, work / (mode + "-best"))
        best["seed"] = best_key[2]
        results[mode] = dict(unshared=unshared, best=best, grammar_histogram=dict(histogram),
                             exact_word_candidates=candidates, finite_contract_checks=checks,
                             symbolic_AX_contract=contract, word_tokens=len(word))
        print(json.dumps(dict(mode=mode, unshared=unshared["total_states"],
                              best=best["total_states"], checks=sum(checks.values()))), flush=True)
    result = dict(driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        python=platform.python_version(), upstream_commit=recover.COMMIT,
        DAG_source_sha256=hashlib.sha256(raw).hexdigest(),
        attribution="Mira-Cult program; Jeff verification; Wade TMBuilder; source08 overlap-safe grammar experiment",
        E="2**a*(2*b+1)-1", formula_tags="4*pair(a,b)+tag; tag=Imp0,Rel1,All2,Eq3",
        source_py_reconstructed=False, full_calculus_theory_rows_retained=True,
        total_new_numeric_codec=True, codec_correctness_formalized=False,
        Lean_simulation_supplied=False, calibrated_consistency_machine_claimed=False,
        proof_search_calibration_supplied=False, bounded_grammar_seeds=args.seeds,
        elapsed_seconds=time.monotonic() - start, liveness=liveness(nodes), variants=results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
