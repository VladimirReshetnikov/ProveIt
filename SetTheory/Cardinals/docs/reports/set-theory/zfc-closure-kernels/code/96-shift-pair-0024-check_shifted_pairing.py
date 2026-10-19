import sys as _assertion_sys
if not __debug__ or _assertion_sys.flags.optimize:
    raise RuntimeError("Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.")
"""Self-authored finite checks; imports/executes no supplied project code.

These checks support, but do not replace, the all-natural-number arguments
in REPORT.md. In particular they do not execute the source machine.
"""
import json
from functools import lru_cache
from pathlib import Path


def pair(a, b):
    return (1 << a) * (2 * b + 1) - 1


def unpair(n):
    a = 0
    while n & 1:
        a += 1
        n //= 2
    return a, n // 2


@lru_cache(None)
def labels(n):
    """All occurring labels, including binders and zero's truth alias."""
    if n == 0:
        return frozenset({0})
    a, b = unpair(n // 4)
    tag = n % 4
    if tag == 0:
        return labels(a) | labels(b)
    if tag == 2:
        return frozenset({a}) | labels(b)
    return frozenset({a, b})


def pack(command, rest):
    selector, fields = command
    for field in reversed(fields):
        rest = pair(field, rest)
    return pair(selector, rest)


def unpack(n):
    selector, n = unpair(n)
    fields = []
    for _ in range(3 if selector >= 3 else 1):
        field, n = unpair(n)
        fields.append(field)
    return (selector, tuple(fields)), n


def main():
    numbers = 65536
    for n in range(numbers):
        a, b = unpair(n)
        assert pair(a, b) == n
        assert a + b <= n and 2 * b <= n
        assert (b < n) == (n > 0)
        assert (a == n) == (n in (0, 1))
        if n:
            assert max(labels(n)) < n
        if n % 4 == 0 and n:
            x, y = unpair(n // 4)
            assert x < n and y < n
        if n % 4 == 2:
            x, y = unpair(n // 4)
            assert x < n and y < n
    pairs = 0
    for a in range(32):
        for b in range(1025):
            n = pair(a, b)
            assert unpair(n) == (a, b)
            assert n >= a + b
            assert (n == 0) == (a == b == 0)
            assert pair(a + 1, b) == 2 * n + 1
            pairs += 1
    commands = [(selector, (x,)) for selector in range(3) for x in range(4)]
    commands += [(selector, (x, y, u)) for selector in range(3, 7)
                 for x in range(4) for y in range(4) for u in range(4)]
    pack_cases = 0
    for command in commands:
        for rest in range(64):
            n = pack(command, rest)
            assert unpack(n) == (command, rest)
            assert rest <= n
            # Later-command fetch receives n+1 and decrements first.
            assert rest < n + 1
            pack_cases += 1
    # Reencoding a formula leaves variable labels alone. Old R(1,1)=17
    # becomes new R(1,1)=21. The old bundle gate (a,b,c)=(21,22,17)
    # passes, but blindly changing matrix c to its new code makes it fail.
    old_c, new_c, a, b = 17, 4 * pair(1, 1) + 1, 21, 22
    assert old_c not in (a, b) and new_c in (a, b)
    result = {
        "status": "PASS",
        "source_code_executed_or_imported": False,
        "numbers_inverse_and_decode_support_checked": numbers,
        "pair_roundtrips_checked": pairs,
        "command_pack_roundtrips_checked": pack_cases,
        "code_zero_labels": sorted(labels(0)),
        "minimum_nonzero_truth_padding": 4 * pair(4 * pair(1, 1), 1),
        "naive_gate_transport_counterexample": {
            "old_a_b_c": [a, b, old_c], "new_matrix_code": new_c,
            "old_gate": True, "blindly_recoded_gate": False},
        "all_values_proof": "REPORT.md",
        "formal_kernel_check": False,
        "binary_machine_compiled": False,
    }
    output = Path(__file__).resolve().parents[1] / 'generated/proof/finite-checks.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
