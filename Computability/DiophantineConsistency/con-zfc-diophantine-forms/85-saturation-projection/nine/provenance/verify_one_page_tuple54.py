#!/usr/bin/env python3
"""Replay the closed arithmetic compact54 coefficient specification.

The only input needed to construct the four integers is COMPACT54_SEED.txt.
All remaining operations are finite sums, products, powers, and nonnegative
integer quotients/remainders. No delivered Python generator is imported.
Optional reference payloads are compared as complete decompressed bytes.
This is a finite numeral identity check, not a native calibration proof.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import time


RESEARCH = Path(__file__).resolve().parents[1]
DIRECTORY = RESEARCH / "candidates/one-page"
EXPECTED = {
    "beta": "456b39f7b82cc935374b729b223221fbf34864e43b699fe94504caad06969d0f",
    "K": "c41628eebbbc8bdfb4ca0246969963713eeffc337039a98cbe075b1727e24aa8",
    "MC": "4164b9c631e09c57f30d0699bd9146c106fed18a2829e5220033d2c06b3001b7",
    "MF_source": "4e094dca3a2cfb839d73f94bfd90ccf9168804d7204f35176b01646885885336",
}
SEED_SHA256 = "5e745601d22ee2cce780db7bac7323ecb7141692c27852fce992f85758d2afab"
TRANSITIONS_SHA256 = "880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def construct(seed):
    # At action index j, state = j//2 and read = j%2. Decode a complete
    # transition from one ten-bit digit of the single fixed seed.
    actions = []
    modes = [(2, 3, 3, 1), (5, 0, 0, 0)]
    for j in range(430):
        action = seed // 1024**j - 1024 * (seed // 1024**(j + 1))
        target = action % 256
        write = action // 256 % 2
        right = action // 512
        require(0 <= target <= 215 and right in (0, 1), "action digit")
        actions.append([j // 2, j % 2, write, 2 * right - 1, target])
        modes.append(((1 - right) * (512 + target),
                      512 + j, right * (256 + target), write))
    require(seed // 1024**430 == 0, "unused high action digits")
    # Exactly 25 additional modes, including the two complemented receivers.
    modes += [(0, 942 + j, 0, 942 + j) for j in range(2)]
    modes += [(0, j, 0, j) for j in range(2)]
    modes += [(0, j % 2 + 942 * (j // 2), 0, 6) for j in range(4)]
    modes += [(2, 2, 2, 0), (3, 4, 4, 698), (4, 4, 4, 0)]
    modes += [(1, 6, 1, 2 + j) for j in range(3)]
    modes += [(j * j, 5, k, 5) for j in range(3) for k in range(3)]
    modes += [(256, 0, 0, 512), (0, 0, 512, 512)]
    require(len(modes) == 457 and len(set(modes)) == 457, "distinct modes")
    require(all(all(0 <= v < 1024 for v in t) for t in modes), "key fields")
    key = [2**30 * w + 2**20 * n + 2**10 * e + s for w, n, e, s in modes]
    # The quotient is 1 precisely for key[j] < key[i], including j=i.
    rank = [0, 1] + [2 + sum((2**40 + key[i] - key[j] - 1) // 2**40
                            for j in range(2, 457)) for i in range(2, 457)]
    require(sorted(rank) == list(range(457)), "arithmetic rank permutation")
    ordered = [modes[0], modes[1]] + sorted(modes[2:])
    require(all(ordered[rank[i]] == modes[i] for i in range(457)),
            "arithmetic rank equals literal lexicographic order")
    rho = 2**89
    base = rho**4831
    h, t = 2**29, 2**42
    coefficient = {}
    for i, (w, n, e, s) in enumerate(modes):
        # Receiver flags also have arithmetic quotient definitions, valid
        # for all 0 <= i <= 456. There is no data-dependent branch here.
        right = (i + 1) // 456 - (i + 1) // 457
        left = i // 456
        label = 2 * w + 2**11 * n + 2**22 * e + 2**32 * s
        c = (1 + 255 * 2**9 * (1 - right) + 255 * 2**18 * (1 - left)
             + 2**27 * (1 - right - left) + h * (1 + label))
        coefficient[rank[i]] = c
    auxiliary = {}
    for offset, width, shift in [(539, 11, 0), (528, 10, 11),
                                  (517, 11, 21), (495, 10, 32)]:
        for j in range(width):
            auxiliary[offset + j] = 2**(29 + shift + j)
    auxiliary[539] += h * t
    for j in range(8):
        auxiliary[567 + j] = 2**(9 + j) + h * (2**(j + 1) + 2**(33 + j))
        auxiliary[575 + j] = 2**(18 + j) + h * (2**(22 + j) + 2**(33 + j))
    auxiliary[583] = 2**27 + h * (2**11 + 2**32)
    auxiliary[1203] = auxiliary[1807] = h * t
    auxiliary[507] = auxiliary[508] = 0
    coefficient.update(auxiliary)
    support = set(coefficient)
    require(len(support) == 520, "support cardinality")
    # Independently expand the display's shorter generating polynomial Phi.
    # Its delta is an arithmetic equality indicator on this fixed range.
    phi = {}

    def add_phi(e, c):
        phi[e] = phi.get(e, 0) + c

    ordinary = 1 + 255 * 2**9 + 255 * 2**18 + 2**27 + h
    for i, (w, n, e, s) in enumerate(modes):
        dr = (2**40 - (i - 455)**2) // 2**40
        dl = (2**40 - (i - 456)**2) // 2**40
        label = 2 * w + 2**11 * n + 2**22 * e + 2**32 * s
        ci = (ordinary - 255 * 2**9 * dr - 255 * 2**18 * dl
              - 2**27 * (dr + dl) + h * label)
        add_phi(rank[i], ci)
    for j in range(11):
        add_phi(539 + j, h * 2**j)
        add_phi(517 + j, h * 2**(21 + j))
    for j in range(10):
        add_phi(528 + j, h * 2**(11 + j))
        add_phi(495 + j, h * 2**(32 + j))
    for e in (539, 1203, 1807):
        add_phi(e, h * t)
    for j in range(8):
        add_phi(567 + j, (2**9 + h * (2 + 2**33)) * 2**j)
        add_phi(575 + j, (2**18 + h * (2**22 + 2**33)) * 2**j)
    add_phi(583, 2**27 + h * (2**11 + 2**32))
    require(phi == {e: c for e, c in coefficient.items() if c},
            "compact Phi expansion equals every literal coefficient")
    dc = sum(rho**e for e in (33, 68, 664, 1268))
    dc += sum(c * (rho**(2409 - e) + rho**(3015 - e))
              for e, c in coefficient.items())
    # Evaluate the displayed rational expression with one exact common
    # denominator. No floating-point approximation or integer truncation.
    denominator = rho**1807
    numerator = sum(c * rho**(1807 - e) for e, c in phi.items())
    scaled = (rho**2409 + rho**3015) * numerator
    require(scaled % denominator == 0, "Phi reciprocal evaluation is integral")
    compact_k = (sum(rho**e for e in (33, 68, 664, 1268))
                 + scaled // denominator + rho**4877)
    require(compact_k == dc + base * rho**46, "compact generating-function K")
    mask = 510 + 2**17 + 2**26 + 2**28 + h * (4 * t - 1)
    mc = base - 1 - sum(rho**e for e in support if e != 1) - 2 * rho**507
    mf = base - 1 + 4 + mask * (rho**2409 + rho**3015)
    mf += sum(rho**(528 + j) for j in range(10))
    mf += sum(rho**(585 + j) for j in range(11)) + rho**1203 + rho**1807
    mf += (2**87 - 1) * sum(rho**e for e in range(4823, 4827))
    mf += (2**38 - 1) * rho**4827
    ports = {"beta": base - 1, "K": dc + base * rho**46,
             "MC": mc, "MF_source": mf}
    return ports, actions, modes, rank


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=Path, default=DIRECTORY / "COMPACT54_SEED.txt")
    parser.add_argument("--reference-dir", type=Path, default=RESEARCH /
                        "candidates/split116-compact/compact54-sharp/coefficients/compact_tuple")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    seed_text = args.seed.read_text()
    require(seed_text.endswith("\n") and seed_text[:-1].isdigit(), "decimal seed syntax")
    require(digest(seed_text.encode()) == SEED_SHA256, "literal decimal seed identity")
    seed = int(seed_text)
    ports, actions, modes, rank = construct(seed)
    records = []
    for name, value in ports.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "little")
        actual_digest = digest(raw)
        require(actual_digest == EXPECTED[name], "authoritative raw identity: " + name)
        reference = args.reference_dir / (name + ".bin.gz")
        require(reference.is_file(), "missing reference payload: " + str(reference))
        require(gzip.decompress(reference.read_bytes()) == raw, "whole-byte identity: " + name)
        records.append({"port": name, "bits": value.bit_length(), "raw_bytes": len(raw),
                        "sha256_raw": actual_digest, "complete_raw_bytes_equal": True})
    receipt = {
        "status": "PASS", "seed_decimal_digits": len(seed_text) - 1,
        "seed_bits": seed.bit_length(), "seed_ascii_sha256": digest(seed_text.encode()),
        "actions": len(actions), "implicit_transition_order": "j=2*state+read",
        "seed_construction_source_sha256": TRANSITIONS_SHA256,
        "mode_count": len(modes), "modes_distinct": True, "support_count": 520,
        "arithmetic_ranks_equal_sorted_order": True,
        "compact_phi_all_coefficients_equal": True,
        "compact_reciprocal_K_exact_and_equal": True,
        "receiver_ranks": {"right": rank[455], "left": rank[456]},
        "ports": records, "seconds": round(time.monotonic() - start, 3),
        "scope": "Complete finite integer identities against the authoritative compact54 tuple. No unbounded native/compiler/calculus theorem is proved by this replay.",
    }
    output = json.dumps(receipt, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
