"""Exact reference algorithms for the finite-window theorems.

These finite checks validate the implementation on the listed examples.
The universal results and their iPRA induction audits are proved in the paper.
Only Python's standard library and exact Fraction arithmetic are used.
"""
from fractions import Fraction as Q
from pathlib import Path
import json


def starts(g, count):
    out = [0]
    for _ in range(count):
        n = out[-1]
        advance = g(n)
        if not isinstance(advance, int) or advance < 0:
            raise ValueError("The control must return a natural number")
        out.append(n + advance + 1)
    return out


def rational_window(sequence, control, bound, epsilon):
    bound, epsilon = Q(bound), Q(epsilon)
    if bound < 0 or epsilon <= 0:
        raise ValueError("Nonnegative range and positive error required")
    budget = int(bound // epsilon)
    nodes = starts(control, budget + 1)
    values = [Q(sequence(n)) for n in nodes]
    if any(x < 0 or x > bound for x in values):
        raise ValueError("Endpoint values violate range contract")
    if any(x > y for x, y in zip(values, values[1:])):
        raise ValueError("Endpoint values violate monotonicity contract")
    ranks = [int(x // epsilon) for x in values]
    for i in range(budget + 1):
        if ranks[i + 1] == ranks[i]:
            return {
                "candidate": i,
                "start": nodes[i],
                "end": nodes[i] + control(nodes[i]),
                "next_start": nodes[i + 1],
                "endpoint_increase": str(values[i + 1] - values[i]),
                "budget": budget,
            }
    raise AssertionError("Finite rise alternative contradicted")


def represented_window(name, control, bound, bits):
    if not isinstance(bound, int) or bound < 0 or bits < 0:
        raise ValueError("Natural range bound and precision required")
    count = (2 ** (bits + 1)) * bound + 1
    nodes = starts(control, count)
    samples = [Q(name(n, bits + 3)) for n in nodes]
    differences = [b - a for a, b in zip(samples, samples[1:])]
    chosen = min(range(count), key=lambda i: differences[i])
    # First-minimum tie breaking is deterministic and finite.
    assert all(differences[chosen] <= d for d in differences)
    assert count * differences[chosen] <= samples[-1] - samples[0]
    return {
        "candidate": chosen,
        "start": nodes[chosen],
        "end": nodes[chosen] + control(nodes[chosen]),
        "next_start": nodes[chosen + 1],
        "observations": count + 1,
        "sample_precision": bits + 3,
        "observed_difference": str(differences[chosen]),
    }


def empty_window(predicate, control, bound):
    if bound < 0:
        raise ValueError("Natural cardinality bound required")
    n = 1
    witnesses = []
    for i in range(bound + 1):
        end = control(n)
        if end < n:
            raise ValueError("Control must dominate its argument")
        hits = [j for j in range(n, end + 1) if predicate(j)]
        if not hits:
            return {"candidate": i, "start": n, "end": end,
                    "earlier_witnesses": witnesses}
        witnesses.append(hits[0])
        n = end + 1
    raise ValueError("The supplied cardinality contract is false")


def truncation_name(sequence, n, bits):
    """Downward dyadic rounding; its error is less than 2^-bits."""
    scale = 2 ** bits
    return Q((sequence(n) * scale).__floor__(), scale)


def validate():
    counts = {"rational_windows": 0, "represented_windows": 0,
              "empty_windows": 0, "invalid_contract_rejections": 0}
    sequences = [
        ("harmonic_approach", lambda n: Q(n, n + 1), 1),
        ("delayed_jump", lambda n: Q(0 if n < 37 else 1), 1),
        ("finite_staircase", lambda n: Q(min(n // 7, 12), 4), 3),
        ("constant_zero", lambda n: Q(0), 0),
    ]
    controls = [lambda n: 0, lambda n: 3,
                lambda n: n + 1, lambda n: 2 * n + 1]
    examples = []
    for label, seq, bound in sequences:
        for control in controls:
            for bits in range(5):
                epsilon = Q(1, 2 ** bits)
                cert = rational_window(seq, control, bound, epsilon)
                assert seq(cert["end"]) - seq(cert["start"]) < epsilon
                counts["rational_windows"] += 1
                for name in [lambda n, p, s=seq: s(n),
                             lambda n, p, s=seq: truncation_name(s, n, p)]:
                    cert = represented_window(name, control, bound, bits)
                    assert seq(cert["next_start"]) - seq(cert["start"]) < epsilon
                    assert seq(cert["end"]) - seq(cert["start"]) < epsilon
                    counts["represented_windows"] += 1
                    if label == "harmonic_approach" and bits == 3:
                        examples.append(cert)
    for finite_set in [set(), {1}, {1, 2, 3}, {3, 8, 30, 111}]:
        for control in [lambda n: n, lambda n: n + 4, lambda n: 2 * n + 1]:
            cert = empty_window(finite_set.__contains__, control, len(finite_set))
            assert not any(n in finite_set for n in range(cert["start"], cert["end"] + 1))
            counts["empty_windows"] += 1
    for action in [lambda: rational_window(lambda n: Q(2), lambda n: 0, 1, Q(1, 2)),
                   lambda: rational_window(lambda n: Q(1, n + 1), lambda n: 0, 1, Q(1, 2)),
                   lambda: empty_window(lambda n: True, lambda n: n, 0)]:
        try:
            action()
        except ValueError:
            counts["invalid_contract_rejections"] += 1
        else:
            raise AssertionError("Invalid contract was accepted")
    return {"status": "passed", "arithmetic": "exact Fraction",
            "counts": counts, "worked_examples": examples,
            "scope": "Finite implementation checks, not universal proofs or embedded iPRA derivations."}


if __name__ == "__main__":
    result = validate()
    dest = Path(__file__).resolve().parent.parent / "validation" / "finite_windows.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], **result["counts"]}, indent=2))
