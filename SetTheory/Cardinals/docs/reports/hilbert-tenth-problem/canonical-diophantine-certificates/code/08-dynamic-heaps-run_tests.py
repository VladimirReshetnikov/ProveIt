#!/usr/bin/env python3
"""Executable checks; not a formal proof or an exhaustive unbounded search."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
from memory_quartic import Event, compile_log, legal_log, bitonic_network, verify_export
from pointer_machine import PointerStacks

ROOT = Path(__file__).resolve().parents[1]

def run() -> dict:
    start = time.perf_counter()
    receipt = {"seed": 20260930, "scope": "finite executable checks, not formal verification"}
    rng = random.Random(receipt["seed"])
    count = 0
    for x in range(10):
        for y in range(10):
            if x == y:
                continue
            solutions = [(b, h) for b in (0, 1) for h in range(12)
                         if (2*b-1)*(y-x) == h+1]
            assert solutions == [(int(x < y), abs(y-x)-1)]
            count += 1
    receipt["strict_comparator_input_pairs"] = count
    for delta in range(20):
        sols = [(z, h) for z in (0, 1) for h in range(21)
                if delta == (1-z)*(h+1) and z*h == 0]
        assert sols == [(1, 0)] if delta == 0 else sols == [(0, delta-1)]
    receipt["zero_test_inputs"] = 20
    guarded = 0
    for selector in (0, 1):
        for residual in range(-20, 21):
            sols = [(u, v) for u in range(21) for v in range(21)
                    if u-v == residual and u*v == 0
                    and selector*u == 0 and selector*v == 0]
            expected = [(max(residual, 0), max(-residual, 0))]
            if selector == 1 and residual != 0:
                expected = []
            assert sols == expected
            guarded += 1
    receipt["guarded_residual_cases"] = guarded
    perms = 0
    for n in (1, 2, 4, 8):
        network = bitonic_network(n)
        k = n.bit_length()-1
        assert len(network) == n*k*(k+1)//4
        for p in itertools.permutations(range(n)):
            v = list(p)
            for i, j, up in network:
                if (v[i] > v[j]) == up:
                    v[i], v[j] = v[j], v[i]
            assert v == list(range(n))
            perms += 1
    receipt["sorting_permutations"] = perms
    alphabet = [Event(a, w, v) for a in range(2) for w in range(2) for v in range(2)]
    logs = valid = 0
    for m in range(5):
        for events in itertools.product(alphabet, repeat=m):
            cert = compile_log(events)
            good = legal_log(events)
            assert (not cert.failures()) == good
            assert (cert.energy() == 0) == good
            assert max((p.degree for _, p in cert.residuals), default=0) <= 2
            logs += 1
            valid += int(good)
    receipt["exhaustive_logs"] = logs
    receipt["valid_exhaustive_logs"] = valid
    print("Exhaustive checks completed", flush=True)
    tests = corrupted = mutations = 0
    for trial in range(24):
        m = rng.randrange(1, 13)
        addresses = [0, 1, 2, 10**70 + rng.randrange(1000)]
        mem = {}
        events = []
        for _ in range(m):
            a = rng.choice(addresses)
            w = rng.randrange(2)
            v = rng.randrange(10000) if w else mem.get(a, 0)
            events.append(Event(a, w, v))
            if w:
                mem[a] = v
        cert = compile_log(events)
        assert not cert.failures()
        assert verify_export(cert.data())
        tests += 1
        # Every changed auxiliary in the first two traces must be rejected.
        if trial < 2:
            for i, role in enumerate(cert.roles):
                if role == "aux":
                    candidate = cert.witness.copy()
                    candidate[i] += 1
                    assert any(p.evaluate(candidate) for _, p in cert.residuals)
                    mutations += 1
        for i, e in enumerate(events):
            if not e.write:
                bad = events.copy()
                bad[i] = Event(e.address, 0, e.value+1)
                bcert = compile_log(bad)
                assert bcert.failures() and bcert.energy() >= 1
                corrupted += 1
    receipt["random_valid_logs"] = tests
    receipt["corrupted_read_logs_rejected"] = corrupted
    receipt["single_auxiliary_mutations_rejected"] = mutations
    # Equality of emitted polynomial shape for equal-length logs.
    a = compile_log([Event(0, 0, 0), Event(3, 1, 4)])
    b = compile_log([Event(999, 1, 18), Event(999, 0, 18)])
    assert a.names == b.names
    assert [p.terms for _, p in a.residuals] == [p.terms for _, p in b.residuals]
    receipt["input_independent_polynomial_shape"] = True
    ptr_tests = 0
    for _ in range(12):
        a, b = PointerStacks(), PointerStacks()
        fresh = rng.sample(range(1000, 1000000), 50)
        nxt = 0
        for t in range(20):
            stack = rng.randrange(2)
            if rng.randrange(2):
                symbol = rng.randrange(3)
                a.push(stack, symbol)
                b.push(stack, symbol, fresh[nxt])
                nxt += 1
            else:
                assert a.pop(stack) == b.pop(stack)
        assert a.normalize() == b.normalize()
        assert legal_log(a.events) and legal_log(b.events)
        assert not compile_log(a.events).failures()
        assert not compile_log(b.events).failures()
        ptr_tests += 1
    receipt["alpha_renamed_pointer_run_pairs"] = ptr_tests
    worked = [Event(7, 1, 4), Event(2, 0, 0), Event(7, 0, 4),
              Event(7, 1, 9), Event(7, 0, 9)]
    c = compile_log(worked)
    (ROOT/"examples"/"memory_certificate.json").write_text(json.dumps(c.data(), indent=2)+"\n")
    (ROOT/"examples"/"memory_events.json").write_text(json.dumps([[e.address,e.write,e.value] for e in worked], indent=2)+"\n")
    receipt["worked_example"] = c.meta
    receipt["elapsed_seconds"] = round(time.perf_counter()-start, 3)
    receipt["all_checks_passed"] = True
    (ROOT/"tests"/"receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    return receipt

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
