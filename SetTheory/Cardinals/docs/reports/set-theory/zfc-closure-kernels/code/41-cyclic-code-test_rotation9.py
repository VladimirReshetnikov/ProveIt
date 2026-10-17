#!/usr/bin/env python3
"""Targeted evidence for rotation9.py; not a formal machine correctness proof."""
import json
from itertools import product
from pathlib import Path
import rotation9 as r


def run():
    results = {}
    for n in range(1000):
        assert r.term_encode(r.term_decode(n)) == n
        assert r.path_encode(r.path_decode(n)) == n
        assert r.step_encode(r.step_decode(n)) == n
        assert r.step_encode(r.step_decode(n, True), True) == n
        assert r.list_encode(list(r.list_decode(n))) == n
    results["codec_roundtrips_per_codec"] = 1000
    malformed_naturals = (-1, True, False, 1.0, "0", None)
    natural_rejections = 0
    for value in malformed_naturals:
        for decoder in (r.term_decode, r.path_decode, r.step_decode,
                        lambda n: list(r.list_decode(n))):
            try:
                decoder(value)
            except ValueError:
                natural_rejections += 1
            else:
                raise AssertionError((decoder, value))
        assert not r.check_code(r.P, r.P, value)
    malformed_terms = (("x",), ("p", r.P), ("n",), ("j", r.P),
                       ("r", r.P, r.P), ("s", r.P), ["p"], "p", None,
                       ("j", r.P, ("x",)))
    for bad_term in malformed_terms:
        assert not r.check_code(bad_term, bad_term, 0)
        assert not r.check_code(r.P, bad_term, 0)
        assert not r.check_code(bad_term, r.P, 0)
        assert not r.check(r.P, r.P, [(2, True, (), bad_term)])
    for bad_step in ((True, False, (), r.P), (0, 0, (), r.P),
                     (0, False, (True,), r.P), (9, False, (), r.P),
                     (0, False), None):
        assert not r.check(r.P, r.P, [bad_step])
    assert not r.check(r.P, r.P, 0)
    assert not r.check_code(r.P, r.P, 0, "yes")
    results["malformed_input_controls"] = {
        "natural_decoder_rejections": natural_rejections,
        "natural_checker_rejections": len(malformed_naturals),
        "malformed_AST_cases": len(malformed_terms),
        "invalid_witness_cases": len(malformed_terms),
        "malformed_step_cases": 6,
        "noniterable_script_rejected": True,
        "nonboolean_option_rejected": True}

    env = {"x": r.P, "y": r.close(r.P), "z": r.neg(r.P)}
    missing = []
    for i, (name, a, b) in enumerate(r.BASIS):
        for rev in (False, True):
            left, right = (b, a) if rev else (a, b)
            extra = sorted(r.variables(right) - r.variables(left))
            if extra:
                missing.append({"rule": name, "reverse": rev, "variables": extra})
            aa, bb = r.substitute(left, env), r.substitute(right, env)
            assert r.rewrite(aa, i, rev, witness=env["y"]) == bb
            assert r.rewrite(r.neg(aa), i, rev, (0,), env["y"]) == r.neg(bb)
    assert missing == [{"rule": "B3", "reverse": True, "variables": ["y"]}]
    results["axiom_orientation_instances"] = 18
    results["nested_context_orientation_instances"] = 18
    results["missing_pattern_variables"] = missing

    inner = r.join(r.P, r.neg(r.P))
    start = r.close(r.rotate(r.rotate(r.rotate(inner))))
    goal = r.join(r.close(r.neg(r.P)), r.close(r.P))
    script = [(7, False, (0,), r.P), (4, False, (), r.P),
              (0, False, (), r.P)]
    assert r.check(start, goal, script)
    encoded = r.list_encode([r.step_encode(s) for s in script])
    assert r.check_code(start, goal, encoded)
    assert not r.check(start, r.neg(goal), script)
    assert not r.check(start, goal, script[:-1])
    assert r.rewrite(start, 7, False, (1,), r.P) is None
    assert r.rewrite(r.join(r.P, r.close(r.neg(r.P))), 3) is None
    results["three_step_certificate"] = {
        "start_prefix": r.prefix(start), "goal_prefix": r.prefix(goal),
        "code": encoded, "script": script,
        "positive": True, "bad_target_rejected": True,
        "truncated_script_rejected": True,
        "bad_path_rejected": True, "repeated_variable_mismatch_rejected": True}

    # The invariant-generator equation is a ground equality, not a schema.
    assert r.rewrite(r.rotate(r.P), 9, invariant=True) == r.P
    assert r.rewrite(r.rotate(r.close(r.P)), 9, invariant=True) is None
    assert r.rewrite(r.rotate(r.P), 9, invariant=False) is None
    ground_script = [(9, False, (), r.P)]
    ground_code = r.list_encode([r.step_encode(s, True) for s in ground_script])
    assert r.check_code(r.rotate(r.P), r.P, ground_code, True)
    results["ground_invariant_generator_control"] = True

    ba = {"j": lambda a, b: a | b, "n": lambda a: 3 ^ a}
    assert r.validate_algebra(r.BASIS[:3], range(4), ba) is None
    choices = (lambda a: a, lambda a: 3 if a else 0)
    sample_terms = [r.P]
    # Mixed trees provide a semantic induction regression, not a proof of it.
    for depth in range(4):
        old = sample_terms[:]
        sample_terms.extend((F, a) for F in ("f", "g", "h", "n")
                            for a in old[:12])
        sample_terms.extend(r.join(a, b) for a, b in zip(old[:12], old[-12:]))
    sample_terms = list(dict.fromkeys(sample_terms))
    product_checks = 0
    for indices in product(range(2), repeat=3):
        f, g, h = (choices[i] for i in indices)
        source = {**ba, "f": f, "g": g, "h": h}
        assert r.validate_algebra(r.df18(), range(4), source) is None
        target = {
            "j": lambda a, b: tuple(x | y for x, y in zip(a, b)),
            "n": lambda a: tuple(3 ^ x for x in a),
            "r": lambda a: (a[1], a[2], a[0]),
            "c": lambda a: (f(a[0]), g(a[1]), h(a[2])),
        }
        # Boolean rows follow componentwise from the separately checked BA.
        assert r.validate_algebra(r.BASIS[3:], list(product(range(4), repeat=3)),
                                  target) is None
        sops = {**target, "s": lambda a: target["n"](target["r"](target["r"](a)))}
        assert r.validate_algebra(r.root8()[3:],
                                  list(product(range(4), repeat=3)), sops) is None
        for term in sample_terms:
            for p in range(4):
                a = r.evaluate(term, {"p": p}, source)
                b = r.evaluate(r.translate(term), {"p": (p, p, p)}, target)
                assert b[0] == a
                folded = r.evaluate(r.fold_to_root8(r.translate(term)),
                                    {"p": (p, p, p)}, sops)
                assert folded == b
                product_checks += 1
    results["product_lift_algebras"] = 8
    results["coordinate_zero_term_checks"] = product_checks
    results["root8_fold_term_checks"] = product_checks
    results["distinct_source_sample_terms"] = len(sample_terms)

    # Essential-commutation negative control: a closure of partition 01|2
    # and a 3-cycle are individually valid, but their conjugates do not commute.
    bad = {
        "j": lambda a, b: a | b, "n": lambda a: 7 ^ a,
        "r": lambda a: ((a << 1) & 7) | (a >> 2),
        "c": lambda a: (3 if a & 3 else 0) | (a & 4),
    }
    assert r.validate_algebra(r.BASIS[:-1], range(8), bad) is None
    failure = r.validate_algebra(r.BASIS, range(8), bad)
    assert failure and failure["row"] == "M"
    results["omitting_M_countermodel"] = failure
    results["metrics"] = r.metrics()
    return results


if __name__ == "__main__":
    result = run()
    destination = Path(__file__).with_name("rotation9_evidence.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
