"""Run reproducible exact checks; writes ../results. No network access needed."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import json
import platform
import sympy as sp
from tubes import Instance, CertificateError, generate, verify
from quartic import compile_certificate, count_gates
from kinetic import build_lift, check_lift, build_offset_lift, check_offset_lift

OUT = Path(__file__).resolve().parents[1] / "results"
OUT.mkdir(exist_ok=True)


def save(name: str, value: dict) -> None:
    (OUT / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def scalar(terms, initial, lower, upper, denominator=1):
    low, high = Q(lower), Q(upper)
    return Instance((tuple((c, (e,)) for c, e in terms),), denominator, (Q(initial),),
                    (((-low.denominator,), -low.numerator),
                     ((high.denominator,), high.numerator)))


def rejected(instance, certificate) -> bool:
    try:
        verify(instance, certificate)
        return False
    except CertificateError:
        return True


def main() -> None:
    chemical_field = (((1,(1,0,1)),), ((-1,(0,1,1)),),
                      ((-2,(2,0,3)),(2,(0,2,3))))
    chemical_initial = (Q(1),Q(1),Q(1,3))
    chemical = Instance(chemical_field, 1, chemical_initial,
                        (((-2000,2000,0),-1), ((1250,-1250,0),1)))
    chemical_wide = Instance(chemical_field, 1, chemical_initial,
                             (((-1,1,0),1), ((1,-1,0),1)))
    examples = [
        ("constant", scalar([(1, 0)], 0, "9/10", "11/10"), 10, 10, 1000, 2, 0, 0),
        ("constant_robust", scalar([(1, 0)], 0, "9/10", "11/10"), 10, 10, 1000, 2, 1, 1),
        ("logistic_robust", scalar([(1, 0), (-1, 2)], 0, "7/10", "41/50"),
         1000, 1000, 10**8, 1, 1, 1),
        ("negative_floor", scalar([(-1, 0)], 0, "-11/10", "-9/10"),
         3, 3, 100, 2, 0, 0),
        ("negative_decay", scalar([(-1, 1)], -1, "-1/2", "-1/5"),
         1000, 1000, 10**8, 2, 0, 0),
        ("pre_blowup", scalar([(1, 2)], 1, "9/5", "11/5"),
         5000, 10000, 10**10, 3, 0, 0),
        ("rational_data", scalar([(1, 0), (1, 1)], "1/2", 1, "6/5", 3),
         1000, 1000, 10**8, 2, 0, 0),
        ("chemical_end_to_end", chemical, 2000, 2000000, 3*10**12, 2, 1, 1),
    ]
    summaries = []
    for name, instance, *args in examples:
        cert = generate(instance, *args)
        result = verify(instance, cert)
        result["name"] = name
        result["noise_units"] = [cert.initial_error_units, cert.forcing_units]
        summaries.append(result)
        save(name+"_certificate.json", {"instance": instance.serializable(),
                                        "certificate": cert.serializable(), "check": result})
    # Independent mutations in every major part of the certificate.
    instance = examples[0][1]
    original = generate(instance, *examples[0][2:])
    mutations = []
    for field in ("nodes", "errors", "floor_remainders", "ceiling_remainders",
                  "scale", "initial_error_units"):
        bad = deepcopy(original)
        if field == "nodes": bad.nodes[1][0] += 1
        elif field == "errors": bad.errors[1] += 1
        elif field == "floor_remainders": bad.floor_remainders[0][0] += 1
        elif field == "ceiling_remainders": bad.ceiling_remainders[0] += 1
        elif field == "scale": bad.scale += 1
        else: bad.initial_error_units += 1
        assert rejected(instance, bad), field
        mutations.append(field)
    assert rejected(instance, generate(instance, 10, 10, 1000, 1))
    unreachable = scalar([], 0, 1, 2)
    assert rejected(unreachable, generate(unreachable, 10, 10, 1000, 2))
    # Small nontrivial circuits, including negative and nonintegral trajectories.
    circuits = []
    for name, inst, n, h, scale, radius in [
        ("constant", instance, 2, 2, 100, 2),
        ("chemical_small", chemical_wide, 1, 10**6, 3*10**12, 2),
        ("negative", scalar([(-1, 1)], -1, "-9/10", "-3/10"), 3, 10, 10000, 2),
        ("negative_floor", scalar([(-1, 0)], 0, "-11/10", "-9/10"), 3, 3, 100, 2),
        ("rational", scalar([(1, 0)], "1/2", "1/2", "7/10", 3), 2, 10, 10000, 2),
    ]:
        cert = generate(inst, n, h, scale, radius)
        compiled = compile_certificate(inst, cert)
        assert compiled["gate_count"] == count_gates(inst, n)
        save(name+"_quartic.json", compiled)
        circuits.append({"name": name, **{key: compiled[key] for key in
                         ("gate_count", "witness_count", "equation_count",
                          "maximum_residual_degree", "all_residuals_zero",
                          "count_formula_verified")}})
    x, z = sp.symbols("x z")
    systems = [((x,), (1-x*x,)), ((x,), (x*x,)),
               ((x,), (sp.Rational(1,3)-2*x,)),
               ((x,z), (z, -x)), ((x,z), (x*z-1, x*x-z)),
               ((x,), (sp.Integer(1),))]
    chemistry = []
    for variables, f in systems:
        lift = build_lift(variables, f)
        chemistry.append(check_lift(lift))
    offset_checks = []
    for variables, f in systems:
        offset_checks.append(check_offset_lift(build_offset_lift(variables, f)))
    offset = build_offset_lift((x,z), (x*z-1,x*x-z))
    save("offset_nonlinear_reactions.json", {
        "species": [str(s) for s in offset.species],
        "field": [str(f) for f in offset.field],
        "clock_factor": str(offset.clock_factor), "reactions": offset.reactions()})
    logistic = build_lift((x,), (1-x*x,))
    save("logistic_reactions.json", {"species": [str(s) for s in logistic.species],
          "initial": ["1", "1", "1/3"], "field": [str(f) for f in logistic.field],
          "clock_factor": str(logistic.clock_factor), "reactions": logistic.reactions()})
    constant_lift = build_lift((x,), (sp.Integer(1),))
    save("constant_flow_reactions.json", {
        "species": [str(s) for s in constant_lift.species], "initial": ["1","1","1/3"],
        "field": [str(f) for f in constant_lift.field],
        "reactions": constant_lift.reactions()})
    # Exhaustive finite checks of both signs in Euclidean floor division,
    # and of exact/upward rounding for the radius rule.
    division_checks = 0
    for dividend in range(-100, 101):
        for divisor in range(1, 21):
            quotient, remainder = divmod(dividend, divisor)
            assert divisor*quotient+remainder == dividend and 0 <= remainder < divisor
            division_checks += 1
    ceiling_checks = 0
    for numerator in range(201):
        for divisor in range(1, 21):
            quotient = (numerator+divisor-1)//divisor
            remainder = divisor*quotient-numerator
            assert 0 <= remainder < divisor
            ceiling_checks += 1
    # Exact symbolic demonstration of the naive dual-rail obstruction.
    p, n = sp.symbols("p n")
    a, b = 1+2*p*n, p*p+n*n
    assert sp.expand((a-b)-(1-(p-n)**2)) == 0
    assert sp.expand((a+b)-(1+(p+n)**2)) == 0
    result = {"python": platform.python_version(), "sympy": sp.__version__,
              "accepted_examples": summaries,
              "rejected_mutations": mutations,
              "other_rejections": ["tube boundary", "unreachable constant trajectory"],
              "quartic_compilations": circuits, "chemical_checks": chemistry,
              "offset_chemical_checks": offset_checks,
              "floor_division_cases": division_checks,
              "ceiling_division_cases": ceiling_checks,
              "naive_lift_obstruction_identities": True,
              "large_chemical_schema_count": {
                  "gate_count": count_gates(chemical, 2000),
                  "witness_count": 2*count_gates(chemical, 2000)+21*2000+11,
                  "equation_count": 2*count_gates(chemical, 2000)+17*2000+11,
                  "full_large_schema_materialized": False},
              "formal_verification": False}
    save("verification_summary.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
