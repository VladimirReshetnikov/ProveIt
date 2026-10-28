"""Independent exact rational and modular verification for new Cauchy tables."""
from fractions import Fraction as F
import json
import sys
from pathlib import Path
from cauchy_kernel import Parameters, Ring, product_tables, recurrent_tables, expected_multiplications


def qa(x, y):
    return (x[0]+y[0], x[1]+y[1])


def qm(x, y):
    a, b = x
    c, d = y
    return (a*c-b*d, a*d+b*c-b*d)


def qi(x):
    a, b = x
    norm = a*a-a*b+b*b
    return ((a-b)/norm, -b/norm)


def qd(x, y):
    return qm(x, qi(y))


def qs(x, c):
    return (x[0]*c, x[1]*c)


def qreduce(x, p):
    mod = 1 << p
    answer = []
    for value in x:
        if value.denominator % 2 == 0:
            raise ArithmeticError("exact rational oracle returned nonintegral value")
        answer.append(value.numerator*pow(value.denominator, -1, mod) % mod)
    return tuple(answer)


def rational_oracle(params):
    """Fresh exact products over Q(U), independent of modular normalization."""
    L, R = 1 << params.a, 1 << params.i
    n = L // 2
    slots = [j % R + 2*R*(j // R) for j in range(n)]
    T = (F(params.t+2*L*params.zeta[0]), F(2*L*params.zeta[1]))
    one, zero = (F(1), F(0)), (F(0), F(0))
    prefactor = one
    for q in range(-L, L):
        if q:
            prefactor = qs(qm(prefactor, (T[0]-q, T[1])), F(1, -q))
    target = [[zero for _ in range(n)] for _ in range(n)]
    source = [[zero for _ in range(n)] for _ in range(n)]
    for b in range(n):
        q = b // R
        E = 2*q-q.bit_count()
        for j in range(n):
            for side in (0, 1):
                difference = slots[j]-slots[b] if side == 0 else slots[b]-slots[j]
                feature = qd(T, (T[0]+difference, T[1]))
                for h in range(b):
                    difference = slots[j]-slots[h] if side == 0 else slots[h]-slots[j]
                    feature = qd(qs(feature, difference), (T[0]+difference, T[1]))
                if side == 0:
                    target[b][j] = qs(qm(prefactor, feature), 1 << E)
                else:
                    source[b][j] = qs(feature, F(1, 1 << E))
    direct = [[qd(qm(prefactor, T), (T[0]+x-y, T[1])) for y in slots] for x in slots]
    return target, source, direct


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def main():
    totals = {"exact_configurations": 0, "modular_configurations": 0,
              "feature_equalities": 0, "modular_kernel_entries": 0,
              "exact_kernel_entries": 0, "operation_count_equalities": 0,
              "zero_prefactor_configurations": 0, "invalid_inputs_rejected": 0}
    for a in range(1, 5):
        for i in range(a):
            for t in (-(1 << i), 1 << i):
                for zeta in ((0, 0), (1, 0), (0, 1), (1, 1), (-1, 2), (2, 0)):
                    params = Parameters(a, i, t, zeta, 32)
                    target_q, source_q, direct_q = rational_oracle(params)
                    n = len(target_q)
                    totals["exact_configurations"] += 1
                    if zeta == (0, 0):
                        totals["zero_prefactor_configurations"] += 1
                    for j in range(n):
                        for k in range(n):
                            reconstructed = (F(0), F(0))
                            for b in range(n):
                                reconstructed = qa(reconstructed, qm(target_q[b][j], source_q[b][k]))
                            require(reconstructed == direct_q[j][k], "exact telescoping failed")
                            totals["exact_kernel_entries"] += 1
                    for precision in (1, 2, 8, 32):
                        params = Parameters(a, i, t, zeta, precision)
                        product, recurrent = product_tables(params), recurrent_tables(params)
                        totals["modular_configurations"] += 1
                        for name, reference in (("target", target_q), ("source", source_q)):
                            require(product[name] == recurrent[name], "product/recurrence disagreement")
                            for b in range(n):
                                for j in range(n):
                                    require(recurrent[name][b][j] == qreduce(reference[b][j], precision),
                                            "modular/exact feature disagreement")
                                    totals["feature_equalities"] += 1
                        for algorithm, result in (("product", product), ("recurrent", recurrent)):
                            actual = result["counts"]["ring_multiplications"]
                            initialization = result["counts"]["initialization_multiplications"]
                            expected = expected_multiplications(params, initialization, algorithm)
                            require(actual == expected, f"operation count mismatch: {actual} != {expected}")
                            totals["operation_count_equalities"] += 1
                        ring = Ring(precision)
                        for j in range(n):
                            for k in range(n):
                                reconstructed = (0, 0)
                                for b in range(n):
                                    reconstructed = ring.add(reconstructed, ring.mul(
                                        recurrent["target"][b][j], recurrent["source"][b][k]))
                                require(reconstructed == qreduce(direct_q[j][k], precision),
                                        "modular reconstruction failed")
                                totals["modular_kernel_entries"] += 1
    # Larger non-prime-ring instances exercise long valuation paths without
    # the rational oracle; exact operation counts remain checked.
    larger_cases = 0
    for a in (5, 6):
        for i in range(a):
            params = Parameters(a, i, -(1 << i), (1, 1), 4*(1 << (a-1))+16)
            product, recurrent = product_tables(params), recurrent_tables(params)
            require(product["target"] == recurrent["target"], "larger target disagreement")
            require(product["source"] == recurrent["source"], "larger source disagreement")
            larger_cases += 1
    for bad in (Parameters(0, 0, 1), Parameters(2, 2, 1), Parameters(2, 0, 0),
                Parameters(2, 0, 4), Parameters(2, 0, 1, precision=0)):
        try:
            recurrent_tables(bad)
        except ValueError:
            totals["invalid_inputs_rejected"] += 1
        else:
            raise ArithmeticError("invalid input accepted")
    result = {"status": "PASS", "method": "self-authored code; no archive code imported or executed",
              "ring": "(Z/2^p Z)[U]/(U^2+U+1)", "totals": totals,
              "larger_product_recurrence_cases": larger_cases,
              "limitations": "Finite component checks, not an end-to-end SAT or formal proof audit."}
    destination = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1] / "results" / "cauchy_checks.json"
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
