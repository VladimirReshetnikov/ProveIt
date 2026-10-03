"""Reproduce exact finite checks and examples; no external dependencies."""
from __future__ import annotations
import copy
from fractions import Fraction
from itertools import product as words
import json
from pathlib import Path
import random
import platform
from collections import Counter
from erasure import (identity, matmul, kron, rank, coordinates, compile_mortality,
                     product, certificate, is_erasing, perturb_numerators, pcp_mortality, information_certificate)
from check_certificate import evaluate

ROOT = Path(__file__).resolve().parents[1]
COUNTS = Counter()


def check(condition: bool, category: str):
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(f"Failed {category} check {COUNTS[category]}")


def write(name: str, data):
    path = ROOT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n")


def delta(b, denom):
    n = len(b)
    return max(Fraction(sum(abs(b[a][i] - b[a][j]) for a in range(n)), 2 * denom)
               for i in range(n) for j in range(n))


def verify_instance(inst):
    n, k, D, K = (inst[x] for x in ("n", "k", "D", "K"))
    h = n - 1
    eta = Fraction(*inst["eta"])
    e, f0 = coordinates(h)
    check(matmul(f0, e) == [[n * x for x in row] for row in identity(h)],
          "coordinate identities")
    check(matmul(e, f0) == [[n * int(i == j) - 1 for j in range(n)]
                            for i in range(n)], "coordinate identities")
    for b, c, v in zip(inst["matrices"], inst["linear_parts"], inst["translations"]):
        check(all(sum(b[a][j] for a in range(n)) == D for j in range(n)),
              "positive stochastic lift")
        check(all((1 - eta) / n < Fraction(x, D) < (1 + eta) / n
                  for row in b for x in row), "positive stochastic lift")
        check(delta(b, D) <= eta, "contraction bounds")
        check(matmul(matmul(f0, b), e) == [[n * n * x for x in row] for row in c],
              "affine block identities")
        eb = [sum(e[i][j] * v[j] for j in range(h)) for i in range(n)]
        check([sum(row) for row in b] == [n * K + n * n * x for x in eb],
              "affine block identities")
    if inst["line_free"] and inst["tensor_degree"] == 2:
        m = inst["source_count"]
        r, l = inst["linear_parts"][m:]
        ri = [[r[i][j] - int(i == j) for j in range(h)] for i in range(h)]
        li = [[l[i][j] - int(i == j) for j in range(h)] for i in range(h)]
        check(rank(ri + li) == h, "guard common-eigenvector obstruction")
        check(rank(matmul(ri, ri)) == 0 and rank(matmul(li, li)) == 0,
              "guard common-eigenvector obstruction")
        br, bl = inst["matrices"][m:]
        check(rank([[br[i][j] - D * int(i == j) for j in range(n)]
                    for i in range(n)]) == n - 1, "guard affine obstruction")
        check([sum(row) for row in br] == [D] * n and
              [sum(row) for row in bl] != [D] * n, "guard affine obstruction")


def verify_words(inst, max_length, rank_every=True):
    m, d, r = inst["source_count"], inst["source_dimension"], inst["tensor_degree"]
    n, k, D = inst["n"], inst["k"], inst["D"]
    eta = Fraction(*inst["eta"])
    accepted = Counter()
    for length in range(1, max_length + 1):
        for w in words(range(k), repeat=length):
            bw = product(inst["matrices"], w)
            projected = [i for i in w if i < m]
            aw = product(inst["source"], projected)
            check(is_erasing(bw) == (rank(aw) == 0), "mortality/erasure equivalence")
            if rank_every:
                check(rank(bw) == 1 + r * rank(aw), "exact tensor rank formula")
            # Test the stronger full linear-part identity, including translations.
            cw = product(inst["linear_parts"], w)
            e, f0 = coordinates(n - 1)
            recovered = matmul(matmul(f0, bw), e)
            factor = n ** (length + 1)
            check(recovered == [[factor * x for x in row] for row in cw],
                  "word block identities")
            if length <= 3:
                check(delta(bw, D ** length) <= eta ** length, "contraction bounds")
            if is_erasing(bw):
                accepted[length] += 1
            if length <= 3:
                result = evaluate(certificate(inst, w))
                check(result["accepted"] == is_erasing(bw), "independent quartic replay")
                small = evaluate(information_certificate(inst, w))
                check(small["accepted"] == is_erasing(bw), "compressed quartic replay")
                h = n - 1
                check(small["variables"] == length * (h * h + k) and
                      small["residuals"] == length * (h * h + 1) + h * h,
                      "compressed certificate size ledger")
                check(result["variables"] == length * (n * n + k) and
                      result["residuals"] == length * (n * n + 1) + n * (n - 1),
                      "certificate size ledger")
    return dict(accepted)


def main():
    # Scalar source alphabets include negative values, zeros, and duplicate labels.
    scalar_instances = []
    for a in range(-2, 3):
        for b in range(-2, 3):
            inst = compile_mortality([[[a]], [[b]]], eta=Fraction(1, 3))
            verify_instance(inst)
            verify_words(inst, 4)
            scalar_instances.append(inst)
    rng = random.Random(20261002)
    for _ in range(8):
        source = [[[rng.randrange(-2, 3) for _ in range(2)] for _ in range(2)]
                  for _ in range(2)]
        inst = compile_mortality(source, eta=Fraction(1, 5))
        verify_instance(inst)
        verify_words(inst, 3)
    nilpotent = [[0, 1, 0], [0, 0, 1], [0, 0, 0]]
    source7 = [nilpotent, identity(3), [[-int(i == j) for j in range(3)]
                                    for i in range(3)],
               [[2, 0, 0], [0, 1, 0], [0, 0, 1]],
               [[1, 1, 0], [0, 1, 0], [0, 0, 1]],
               [[1, 0, 0], [0, 1, 1], [0, 0, 1]]]
    inst7 = compile_mortality(source7, eta=Fraction(1, 10))
    verify_instance(inst7)
    probabilities7 = verify_words(inst7, 3)
    write("examples/seven_state_instance.json", inst7)
    cert7 = certificate(inst7, [0, 0, 0])
    write("examples/seven_state_erasure_certificate.json", cert7)
    write("examples/seven_state_uniform_certificate.json", certificate(inst7, [0, 0, 0], "uniform"))
    # A minimal readable example: one scalar source generator 0, plus two guards.
    tiny = compile_mortality([[[0]]], eta=Fraction(1, 2))
    verify_instance(tiny)
    counts_tiny = verify_words(tiny, 5)
    write("examples/three_state_instance.json", tiny)
    # A source letter followed by the translated guard is rank one but not J.
    c = certificate(tiny, [0, 2])
    check(evaluate(c)["accepted"], "rank-one versus uniform distinction")
    uniform = certificate(tiny, [0, 2], "uniform")
    check(not evaluate(uniform)["accepted"], "rank-one versus uniform distinction")
    write("examples/three_state_nonuniform_erasure_certificate.json", c)
    write("examples/three_state_wrong_uniform_target.json", uniform)
    for t in range(1, 6):
        check(counts_tiny[t] == 3 ** t - 2 ** t, "iid erasure counts")
    compressed = information_certificate(tiny, [0, 2])
    for t in range(2):
        for a in range(2):
            for b in range(2):
                bad = copy.deepcopy(compressed)
                bad["information_prefixes"][t][a][b] += 1
                check(not evaluate(bad)["accepted"], "compressed adversarial mutations")
    write("examples/three_state_information_certificate.json", compressed)
    small7 = information_certificate(inst7, [0, 0, 0])
    write("examples/seven_state_information_certificate.json", small7)
    # Mutations target each type of residual and exact-domain validation.
    for pos in range(len(c["prefixes"])):
        for a in range(3):
            for b in range(3):
                mutated = copy.deepcopy(c)
                mutated["prefixes"][pos][a][b] += 1
                check(not evaluate(mutated)["accepted"], "adversarial certificate mutations")
    for t in range(2):
        for i in range(3):
            bad = copy.deepcopy(c)
            bad["selectors"][t][i] += 1
            check(not evaluate(bad)["accepted"], "adversarial certificate mutations")
    for value in (1.0, True, -1, "1"):
        bad = copy.deepcopy(c)
        bad["selectors"][0][0] = value
        try:
            evaluate(bad)
        except ValueError:
            check(True, "strict natural-domain checks")
        else:
            check(False, "strict natural-domain checks")
    # Arbitrarily small invertibilizing perturbations; invariant-space equivalence
    # itself is the exact affine identity in the proof, not a finite test.
    good_q = []
    for q in range(2, 82):
        perturbed = perturb_numerators(tiny, q)
        all_invertible = all(rank(b) == 3 for b in perturbed["matrices"])
        check(all_invertible, "invertibilizing perturbations")
        if all_invertible:
            good_q.append(q)
    write("examples/perturbed_non_erasing_instance.json", perturb_numerators(tiny, 1000))
    # Baseline doubly stochastic embedding.
    base = compile_mortality([[[0, 1], [0, 0]], [[1, 0], [0, 1]]], line_free=False)
    verify_instance(base)
    verify_words(base, 4)
    check(all(sum(row) == base["D"] for b in base["matrices"] for row in b),
          "doubly stochastic special case")
    # Higher tensor extension; the generated guard algebra spans all 3x3 matrices.
    higher = compile_mortality([[[0, 1], [0, 0]]], tensor_degree=3)
    verify_instance(higher)
    verify_words(higher, 3)
    p = [[0, 0, 1], [1, 0, 0], [0, 1, 0]]
    q = [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
    span = []
    for w in words(range(2), repeat=6):
        # Shorter words supplied via prefixes as well.
        for j in range(7):
            a = product([p, q], w[:j])
            span.append([x for row in a for x in row])
    check(rank(span) == 9, "higher-tensor guard algebra")
    # Sharp commuting horizon: a single h-dimensional nilpotent shift needs h steps.
    for h in range(1, 7):
        shift = [[int(j == i + 1) for j in range(h)] for i in range(h)]
        comm = compile_mortality([shift], line_free=False)
        for t in range(1, h + 1):
            check(is_erasing(product(comm["matrices"], [0] * t)) == (t == h),
                  "sharp commuting horizon examples")
    # Full connector-word tests, including empty strings and adjacent connectors.
    pcp_cases = [[("a", "ab"), ("ba", "a")],
                 [("a", "b")], [("", "")], [("a", "")],
                 [("ab", "ab"), ("", "a")],
                 [("a", "bb"), ("b", "aa")],
                 [("a", "ab"), ("b", "ba")]]
    for tiles in pcp_cases:
        matrices = pcp_mortality(tiles)
        connector = len(tiles)
        check(matmul(matrices[-1], matrices[-1]) == matrices[-1],
              "PCP connector idempotence")
        for length in range(1, 6):
            for w in words(range(len(matrices)), repeat=length):
                positions = [j for j, i in enumerate(w) if i == connector]
                matching_gap = False
                for left, right in zip(positions, positions[1:]):
                    gap = w[left + 1:right]
                    if gap and ("".join(tiles[i][0] for i in gap) ==
                                "".join(tiles[i][1] for i in gap)):
                        matching_gap = True
                actual = product(matrices, w)
                check((rank(actual) == 0) == matching_gap,
                      "PCP full-word reduction")
    pcp_tiles = [("a", "ab"), ("ba", "a")]
    pcp_inst = compile_mortality(pcp_mortality(pcp_tiles), eta=Fraction(1, 4))
    verify_instance(pcp_inst)
    pcp_cert = certificate(pcp_inst, [2, 0, 1, 2])
    check(evaluate(pcp_cert)["accepted"], "PCP stochastic end-to-end certificate")
    pcp_inst["pcp_tiles"] = pcp_tiles
    write("examples/pcp_nine_state_instance.json", pcp_inst)
    write("examples/pcp_nine_state_certificate.json", pcp_cert)
    pcp_small = information_certificate(pcp_inst, [2, 0, 1, 2])
    write("examples/pcp_nine_state_information_certificate.json", pcp_small)
    check(evaluate(pcp_small)["accepted"], "PCP compressed end-to-end certificate")
    results = {"status": "passed", "python": platform.python_version(),
               "random_seed": 20261002, "assertions": sum(COUNTS.values()),
               "categories": dict(sorted(COUNTS.items())),
               "seven_state_K": inst7["K"], "seven_state_D": inst7["D"],
               "seven_state_certificate": evaluate(cert7),
               "seven_state_erasing_words_by_length": probabilities7,
               "pcp_certificate": evaluate(pcp_cert),
               "seven_state_information_certificate": evaluate(small7),
               "pcp_information_certificate": evaluate(pcp_small),
               "three_state_K": tiny["K"], "three_state_D": tiny["D"],
               "three_state_erasing_words_by_length": counts_tiny,
               "perturbation_q_values_checked": good_q,
               "scope": "Exact finite checks, not formal verification or proof of undecidability."}
    write("verification/check_results.json", results)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
