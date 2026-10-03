"""Reproducible finite exact checks. Run from any working directory."""
from __future__ import annotations
import itertools
import json
import sys
from pathlib import Path
from clock_certificates import *

ROOT = Path(__file__).resolve().parents[1]
results: dict[str, object] = {}

def check_gadget() -> None:
    checks = 0
    for d in range(-8,9):
        for s in range(3):
            zeros = []
            for a in range(11):
                for b in range(11):
                    val = (d-a+b)**2 + a*b + s*(a+b)
                    assert val >= 0
                    if val == 0: zeros.append((a,b))
                    checks += 1
            expected = [(max(d,0),max(-d,0))] if s == 0 or d == 0 else []
            assert zeros == expected
    results["gadget_assignments_checked"] = checks


def check_stack() -> None:
    checks = 0
    for u in range(64):
        assert encode_stack(decode_stack(u)) == u
        for v in range(130):
            for op in sorted(OPS):
                nxt = literal_stack_step(decode_stack(u), op)
                expected = nxt is not None and encode_stack(nxt) == v
                assert (stack_residual(op,u,v) == 0) == expected
                checks += 1
    results["stack_operation_pairs_checked"] = checks


def check_transitions() -> None:
    machine = example_machine()
    checks = 0
    for old in itertools.product(range(3),range(6),range(6)):
        for new in itertools.product(range(3),range(6),range(6)):
            for rule in machine.rules:
                ds = (old[0]-rule.source,new[0]-rule.target,
                      stack_residual(rule.left,old[1],new[1]),
                      stack_residual(rule.right,old[2],new[2]))
                assert all(d == 0 for d in ds) == (literal_step(old,rule) == new)
                checks += 1
    results["labelled_transition_candidates_checked"] = checks


def all_traces(machine: Machine, horizon: int):
    todo = [((),machine.initial)]
    for _ in range(horizon):
        nxt = []
        for labels, config in todo:
            for i,r in enumerate(machine.rules):
                result = literal_step(config,r)
                if result is not None: nxt.append((labels+(i,),result))
        todo = nxt
    return [labels for labels,_ in todo]


def tick_count(machine: Machine, labels, deadline):
    config = machine.initial
    count = 0
    for r in labels[:deadline]:
        config = literal_step(config,machine.rules[r])
        assert config is not None
        count += int(config[0] in machine.accepting)
    return count


def check_traces() -> None:
    machine = example_machine()
    cases = accepted = rejected = 0
    for horizon in range(7):
        dsets = [()]
        if horizon: dsets.extend([(horizon,), (1,horizon)])
        for deadlines in dsets:
            cert = compile_certificate(machine,horizon,deadlines)
            for labels in all_traces(machine,horizon):
                good = all(tick_count(machine,labels,d) >= i
                           for i,d in enumerate(deadlines,start=1))
                try:
                    values = cert.canonical(labels)
                except ValueError:
                    assert not good
                    rejected += 1
                else:
                    assert good and cert.validate(values)
                    accepted += 1
                cases += 1
    cert = compile_certificate(machine,5,(4,))
    values = cert.canonical((1,2,4,5,6))
    mutations = 0
    for name in cert.variables:
        for diff in (-1,1):
            if values[name]+diff < 0: continue
            changed = dict(values)
            changed[name] += diff
            assert not cert.validate(changed)
            mutations += 1
    assert not cert.validate({**values,"extraneous":0})
    negative = dict(values); negative["q_0"] = -1
    assert not cert.validate(negative)
    cert.export(str(ROOT/"examples"/"quadratic_certificate.json"),values)
    results.update(trace_deadline_cases=cases, accepted_canonical_certificates=accepted,
                   rejected_deadline_cases=rejected, one_coordinate_mutations_rejected=mutations,
                   example_variables=len(cert.variables), example_degree=cert.polynomial.degree,
                   example_monomials=len(cert.polynomial.terms))


def toy_approximation(stage: int, bit: int) -> int:
    answer = bit % 2
    if bit == 0 and 3 <= stage <= 5: answer ^= 1
    if bit == 1 and stage <= 2: answer ^= 1
    return answer


def check_tree() -> None:
    true_path = first_matches(10,toy_approximation,lambda j:j%2)
    assert true_path == (1,6,6,6,6,6,7,8,9,10)
    assert true_path[0] == 1 and toy_approximation(3,0) != toy_approximation(1,0)
    assert first_match_tree(true_path,toy_approximation)
    checked = accepted = 0
    for length in range(5):
        for node in itertools.product(range(8),repeat=length):
            good = first_match_tree(node,toy_approximation)
            if good:
                accepted += 1
                assert all(first_match_tree(node[:j],toy_approximation)
                           for j in range(length+1))
            checked += 1
    # A temporarily plausible wrong first-bit claim cannot extend beyond stage 5.
    assert first_match_tree((3,),toy_approximation)
    assert not any(first_match_tree((3,)+tail,toy_approximation)
                   for tail in itertools.product(range(6,8),repeat=2))
    results.update(first_match_tree_nodes_checked=checked,
                   first_match_tree_nodes_accepted=accepted,
                   toy_first_match_path=list(true_path),
                   early_match_is_not_a_settling_time=True)


def check_bad_inputs() -> None:
    bad = 0
    tests = [lambda: Rule(-1,0), lambda: Rule(0,0,"bad"),
             lambda: compile_certificate(example_machine(),-1),
             lambda: compile_certificate(example_machine(),2,(3,)),
             lambda: compile_certificate(example_machine(),2,(-1,)),
             lambda: compile_certificate(example_machine(),2,(True,)),
             lambda: decode_stack(-1)]
    for action in tests:
        try: action()
        except (ValueError,TypeError): bad += 1
        else: raise AssertionError("Expected invalid-input rejection")
    results["invalid_inputs_rejected"] = bad

if __name__ == "__main__":
    for fn in (check_gadget,check_stack,check_transitions,check_traces,check_tree,check_bad_inputs):
        fn()
    results["status"] = "PASS"
    results["scope"] = "Finite exact checks only; no infinitary or proof-assistant verification"
    results["python"] = sys.version.split()[0]
    target = ROOT/"test_results.json"
    target.write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(results,indent=2))
