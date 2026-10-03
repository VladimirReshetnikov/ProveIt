#!/usr/bin/env python3
"""Independent audit of the sequential-cleanup reset-net compilation.

Reads, but does not import, the compiler and supplied trace artifacts.  All
transition firing, invariant checking, and ledger counts below are independent.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent


def fire(net, marking, tr):
    if any(marking.get(p, 0) < w for p, w in tr["pre"].items()):
        raise ValueError("disabled: " + tr["name"])
    after = {p: marking.get(p, 0) - tr["pre"].get(p, 0)
             for p in net["places"]}
    loss = sum(after[p] for p in tr["reset"])
    for p in tr["reset"]:
        after[p] = 0
    for p, w in tr["post"].items():
        after[p] += w
    return {p: n for p, n in after.items() if n}, loss


def main():
    program = json.loads((ROOT / "source/virtual3.json").read_text())
    net = json.loads((ROOT / "reset_net.json").read_text())
    supplied = json.loads((ROOT / "source/accepting_counter_trace.json").read_text())
    regs = program["registers"]
    assert regs == ["L", "R", "T"]
    rows = program["rows"]
    assert len(rows) == len(set(rows))
    assert program["halt"] not in rows
    assert len(net["places"]) == len(set(net["places"]))
    trans = {t["name"]: t for t in net["transitions"]}
    assert len(trans) == len(net["transitions"])
    assert set(net["data_places"]) == set(regs + ["reserve", "budget"])
    assert net["target"] == {"q:DONE": 1}
    assert net["initial_affine"] == {
        "L": {"L": 1}, "R": {"R": 1}, "budget": {"L": 1, "R": 1},
        "q:START": {"constant": 1}}

    expected = []

    def expect(name, src, dst, pre=None, post=None, reset=None):
        a = {"q:" + src: 1, **(pre or {})}
        b = {"q:" + dst: 1, **(post or {})}
        t = trans[name]
        assert (t["pre"], t["post"], t["reset"]) == (a, b, reset or [])
        assert (t["source_control"], t["target_control"]) == (src, dst)
        expected.append(name)

    expect("pump", "START", "START", post={"reserve": 1, "budget": 1})
    expect("enter", "START", program["entry"])
    for label, row in rows.items():
        op, r, *dst = row
        for q in dst:
            assert q in rows or q == program["halt"]
        if op == "ADD":
            expect(label + ":inc", label, dst[0], {"reserve": 1}, {regs[r]: 1})
        else:
            assert op == "SUB"
            expect(label + ":pos", label, dst[0], {regs[r]: 1}, {"reserve": 1})
            expect(label + ":zero", label, dst[1], reset=[regs[r]])
    phases = [program["halt"], "CLEAN_R", "CLEAN_T", "DRAIN"]
    for i, reg in enumerate(regs):
        expect("clean_" + reg, phases[i], phases[i], {reg: 1}, {"reserve": 1})
        expect("advance_" + reg, phases[i], phases[i + 1])
    expect("drain", "DRAIN", "DRAIN", {"reserve": 1, "budget": 1})
    expect("finish", "DRAIN", "DONE")
    assert set(expected) == set(trans)

    kinds = Counter(t["kind"] for t in trans.values())
    ledger = {
        "places": len(net["places"]), "control_places": len(net["control_places"]),
        "data_places": len(net["data_places"]), "transitions": len(trans),
        "ordinary_input_arcs": sum(len(t["pre"]) for t in trans.values()),
        "ordinary_output_arcs": sum(len(t["post"]) for t in trans.values()),
        "reset_arcs": sum(len(t["reset"]) for t in trans.values()),
        "transition_kinds": dict(kinds),
    }
    ledger["ordinary_arcs"] = ledger["ordinary_input_arcs"] + ledger["ordinary_output_arcs"]
    for key in ("places", "control_places", "data_places", "transitions",
                "ordinary_input_arcs", "ordinary_output_arcs", "ordinary_arcs", "reset_arcs"):
        assert ledger[key] == json.loads((ROOT / "net_ledger.json").read_text())[key]
    assert (ledger["places"], ledger["transitions"], ledger["ordinary_arcs"],
            ledger["reset_arcs"]) == (539, 771, 2608, 233)
    assert all(w == 1 for t in trans.values() for a in ("pre", "post") for w in t[a].values())

    x = [supplied["input"][r] for r in regs]
    assert x[2] == 0
    values, q = x[:], program["entry"]
    states, source_word = [values[:]], []
    for j, given in enumerate(supplied["trace"]):
        assert given["step"] == j
        assert (given["control"], given["registers"]) == (q, values)
        op, reg, *dst = rows[q]
        if op == "ADD":
            source_word.append(q + ":inc")
            values[reg] += 1
            q = dst[0]
        elif values[reg]:
            source_word.append(q + ":pos")
            values[reg] -= 1
            q = dst[0]
        else:
            source_word.append(q + ":zero")
            q = dst[1]
        assert (given["next_control"], given["next_registers"]) == (q, values)
        states.append(values[:])
    assert q == supplied["final_control"] == program["halt"]
    assert values == supplied["final_registers"]
    masses = [sum(s) for s in states]
    h, B, H, M = len(source_word), masses[0], masses[-1], max(masses)
    K = M - B
    N = h + H + B + 2 * K + 5
    assert (h, B, H, M, K, N) == (328, 6, 11, 25, 19, 388)

    # Audit the local quadratic peak constraints, including unique integer values.
    u, v, previous_peak = [], [0], B
    for j in range(1, h + 1):
        u.append(max(masses[j] - previous_peak, 0))
        v.append(max(previous_peak - masses[j], 0))
        assert masses[j-1] + v[j-1] + u[-1] - masses[j] - v[j] == 0
        assert u[-1] * v[j] == 0
        previous_peak = masses[j] + v[j]
        assert previous_peak == max(masses[:j+1])
    assert sum(u) == H + v[h] - B == K
    assert N - h - 3 * H + B - 2 * v[h] - 5 == 0

    def initial():
        return {p: n for p, n in {**dict(zip(regs, x)), "budget": B, "q:START": 1}.items() if n}

    def check_invariant(marking, loss):
        assert marking.get("budget", 0) - marking.get("reserve", 0) - sum(marking.get(p, 0) for p in regs) == loss
        assert sum(marking.get(p, 0) for p in net["control_places"]) == 1

    def word_for(k):
        word = ["pump"] * k + ["enter"] + source_word[:]
        for reg, n in zip(regs, values):
            word += ["clean_" + reg] * n + ["advance_" + reg]
        return word + ["drain"] * (B + k) + ["finish"]

    checks = []
    for k in (K, K + 1, K + 5):
        marking, loss = initial(), 0
        word = word_for(k)
        check_invariant(marking, loss)
        for name in word:
            marking, current_loss = fire(net, marking, trans[name])
            loss += current_loss
            check_invariant(marking, loss)
        assert marking == net["target"] and loss == 0
        assert len(word) == h + H + B + 2 * k + 5
        checks.append({"k": k, "length": len(word), "target_reached": True})
        if k == K:
            (OUT / "shortest_accepting_word.json").write_text(json.dumps(word, indent=2) + "\n")

    # The faithful path at the next smaller fuel really fails at an increment.
    assert K > 0
    marking, loss = initial(), 0
    fail = None
    for j, name in enumerate(word_for(K - 1)):
        try:
            marking, current_loss = fire(net, marking, trans[name])
        except ValueError:
            fail = {"k": K - 1, "word_index": j, "transition": name,
                    "reserve_at_failure": marking.get("reserve", 0)}
            assert name.endswith(":inc") and not marking.get("reserve", 0)
            break
        loss += current_loss
        check_invariant(marking, loss)
    assert fail is not None

    # A deliberately false zero guess is enabled but creates irreversible debt.
    marking, loss = initial(), 0
    bad_zero = None
    for name in ["pump"] * K + ["enter"] + source_word:
        if name.endswith(":pos"):
            bad_name = name[:-3] + "zero"
            before = marking
            marking, current_loss = fire(net, marking, trans[bad_name])
            loss += current_loss
            assert loss > 0
            check_invariant(marking, loss)
            bad_zero = {"transition": bad_name, "reset_loss": loss,
                        "debt_after_false_zero": marking.get("budget", 0) - marking.get("reserve", 0) - sum(marking.get(p, 0) for p in regs)}
            break
        marking, current_loss = fire(net, marking, trans[name])
        loss += current_loss
        check_invariant(marking, loss)
    assert bad_zero is not None

    result = {"status": "PASS", "ledger": ledger,
              "source": {"h": h, "B": B, "H": H, "M": M, "K": K, "shortest_length": N,
                         "last_peak_slack": v[h]},
              "accepting_checks": checks, "insufficient_fuel_check": fail,
              "false_zero_check": bad_zero,
              "canonical_peak_extension": {"added_variables": 2*h, "added_affine_squares": h,
                                           "added_nonnegative_products": h}}
    (OUT / "audit_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
