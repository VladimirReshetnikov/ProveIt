"""Independent natural-domain quartic evaluator: imports no generator code."""
from __future__ import annotations
import json
import sys
from pathlib import Path


def natural(x, label: str, positive: bool = False):
    if type(x) is not int or x < (1 if positive else 0):
        raise ValueError(f"{label}: expected {'positive' if positive else 'natural'} integer")
    return x


def array(x, length: int, label: str):
    if type(x) is not list or len(x) != length:
        raise ValueError(f"{label}: wrong array length or type")
    return x


def matrix(x, n: int, label: str, positive: bool = False):
    array(x, n, label)
    for row in x:
        array(row, n, label)
        for v in row:
            natural(v, label, positive)
    return x


def evaluate_information(data: dict) -> dict:
    n = natural(data["n"], "n", True)
    if n < 2:
        raise ValueError("Information certificate requires n>=2")
    h = n - 1
    k = natural(data["k"], "k", True)
    tmax = natural(data["T"], "T", True)
    D = natural(data["D"], "D", True)
    mats = array(data["matrices"], k, "matrices")
    for b in mats:
        matrix(b, n, "matrix", True)
        if any(sum(b[a][j] for a in range(n)) != D for j in range(n)):
            raise ValueError("Wrong column sum")
    cs = [[[b[a][c] - b[a][h] for c in range(h)] for a in range(h)] for b in mats]
    selectors = array(data["selectors"], tmax, "selectors")
    ys = array(data["information_prefixes"], tmax, "information prefixes")
    old = [[int(a == b) + 1 for b in range(h)] for a in range(h)]
    power = 1
    residuals, decoded = [], []
    for t in range(tmax):
        s = array(selectors[t], k, "selectors")
        for v in s:
            natural(v, "selector")
        y = matrix(ys[t], h, "information prefix")
        residuals.append(sum(s) - 1)
        decoded.append(s.index(1) if sum(s) == 1 else None)
        next_power = D * power
        for a in range(h):
            for b in range(h):
                rhs = sum(s[i] * sum(cs[i][a][c] * (old[c][b] - power)
                                    for c in range(h)) for i in range(k))
                residuals.append(y[a][b] - next_power - rhs)
        old, power = y, next_power
    residuals += [old[a][b] - power for a in range(h) for b in range(h)]
    if "word" in data:
        w = array(data["word"], tmax, "word")
        if any(type(i) is not int or not 0 <= i < k for i in w):
            raise ValueError("Invalid word metadata")
        if None not in decoded and w != decoded:
            raise ValueError("Word metadata disagrees with selectors")
    value = sum(v * v for v in residuals)
    return {"accepted": value == 0, "quartic_value": value,
            "variables": tmax * (h * h + k), "residuals": len(residuals),
            "nonzero_residuals": sum(v != 0 for v in residuals),
            "decoded_word": decoded}


def evaluate(data: dict) -> dict:
    if data.get("format") == "exact-erasure-information-quartic-v1":
        return evaluate_information(data)
    if data.get("format") != "exact-erasure-natural-quartic-v1":
        raise ValueError("Unsupported certificate format")
    n = natural(data["n"], "n", True)
    k = natural(data["k"], "k", True)
    tmax = natural(data["T"], "T", True)
    denom = natural(data["D"], "D", True)
    mats = array(data["matrices"], k, "matrices")
    for b in mats:
        matrix(b, n, "matrix", True)
        if any(sum(b[i][j] for i in range(n)) != denom for j in range(n)):
            raise ValueError("Input matrix does not have the declared column sum")
    selectors = array(data["selectors"], tmax, "selectors")
    prefixes = array(data["prefixes"], tmax, "prefixes")
    old = [[int(i == j) for j in range(n)] for i in range(n)]
    residuals = []
    decoded = []
    for t in range(tmax):
        s = array(selectors[t], k, "selector")
        for v in s:
            natural(v, "selector")
        x = matrix(prefixes[t], n, "prefix")
        residuals.append(sum(s) - 1)
        decoded.append(s.index(1) if sum(s) == 1 else None)
        for a in range(n):
            for b in range(n):
                rhs = sum(s[i] * sum(mats[i][a][c] * old[c][b] for c in range(n))
                          for i in range(k))
                residuals.append(x[a][b] - rhs)
        old = x
    target = data["target"]
    if target == "rank_one":
        residuals += [old[a][b] - old[a][0] for a in range(n) for b in range(1, n)]
    elif target == "uniform":
        residuals += [old[a][b] - old[0][0] for a in range(n) for b in range(n)
                      if (a, b) != (0, 0)]
    else:
        raise ValueError("Unsupported terminal target")
    if "word" in data:
        w = array(data["word"], tmax, "word")
        if any(type(i) is not int or not 0 <= i < k for i in w):
            raise ValueError("Invalid word metadata")
        # Metadata is not a polynomial variable, and is checked separately.
        if None not in decoded and w != decoded:
            raise ValueError("Word metadata disagrees with selectors")
    val = sum(x * x for x in residuals)
    return {"accepted": val == 0, "quartic_value": val,
            "variables": tmax * (n * n + k), "residuals": len(residuals),
            "nonzero_residuals": sum(x != 0 for x in residuals),
            "decoded_word": decoded}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python check_certificate.py certificate.json")
    try:
        result = evaluate(json.loads(Path(sys.argv[1]).read_text()))
    except (ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit(f"Invalid certificate: {exc}") from exc
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["accepted"] else 1)


if __name__ == "__main__":
    main()
