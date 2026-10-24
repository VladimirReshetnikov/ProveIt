#!/usr/bin/env python3
"""Reconstruct all four BFS compact44 constants from the printed finite recipe.

No network, search procedure or consistency assumption is used.  The seed is
the literal 436-character integer in ProveIt's frozen complete equation page.
Binary payloads use unsigned little-endian representation.
"""
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
SEED = (
    "BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y"
    "iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U"
    "OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq"
    "4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ"
    "FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F"
    "We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl"
    "0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ"
    "8P"
)
EXPECTED = {
    "beta": ("beta.bin.gz", "0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d"),
    "K0": ("K.bin.gz", "4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7"),
    "MC": ("MC.bin.gz", "6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4"),
    "MF": ("MF_source.bin.gz", "48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def decoded_actions():
    require(len(SEED) == 436, "seed length")
    encoded = 0
    for symbol in SEED:
        encoded = 62 * encoded + ALPHABET.index(symbol)
    n = encoded % 2**636
    t0 = (encoded // 2**636) % 2**1675
    e0 = encoded // 2**2311
    flags = [(n >> j) & 1 for j in range(430)]
    masks = [(n >> (430 + q)) & 1 for q in range(215)]
    prefix = [0]
    for flag in flags:
        prefix.append(prefix[-1] + flag)
    mask_prefix = [0]
    for mask in masks:
        mask_prefix.append(mask_prefix[-1] + mask)
    result = []
    for j in range(430):
        q, b = divmod(j, 2)
        f = 14 if not masks[q] else (e0 // 16**mask_prefix[q]) % 16
        u = 1 + prefix[j] if flags[j] else (t0 // 216**(j - prefix[j])) % 216
        v, d = (f >> (2 * b)) & 1, (f >> (2 * b + 1)) & 1
        result.append((u, v, d))
    require(result[0] == (1, 1, 1), "corrected first transition")
    return result


def tile_coefficients(actions):
    right = {u for u, v, d in actions if d == 1}
    left = {u for u, v, d in actions if d == 0}
    h = lambda q, b: 2 * (q + 1) + b
    rr = {q: 6 + sum(z < q for z in right) for q in right}
    ll = {q: 205 + sum(z < q for z in left) for q in left}
    tiles = set()
    for j, (u, v, d) in enumerate(actions):
        q, b = divmod(j, 2)
        tiles.add((0 if d else ll[u], h(q, b), rr[u] if d else 0, v))
    for b in (0, 1):
        tiles.add((0, h(215, b), 0, h(215, b)))
        tiles.add((0, b, 0, b))
    tiles.update((rr[q], b, 0, h(q, b)) for q in right for b in (0, 1))
    tiles.update((0, b, ll[q], h(q, b)) for q in left for b in (0, 1))
    tiles.update((0, t, 0, 438) for t in (0, 1, 432, 433))
    tiles.update({(2, 434, 2, 0), (2, 435, 3, 1),
                  (3, 436, 4, h(actions[0][0], 0)), (4, 436, 4, 0), (5, 0, 0, 0)})
    tiles.update((1, 438, 1, t) for t in (434, 435, 436))
    tiles.update((a, 437, b, 437) for a in (0, 1, 4) for b in (0, 1, 2))
    require(len(tiles) == 943, "tile cardinality")
    start, finish = (2, 435, 3, 1), (5, 0, 0, 0)
    def key(tile):
        w, n, e, s = tile
        return 2**30 * w + 2**20 * n + 2**10 * e + s
    ordered = [start, finish] + sorted(tiles - {start, finish}, key=key)
    require(len({key(t) for t in tiles}) == 943, "rank uniqueness")
    coefficients = {j: 1 + 2**51 for j in range(943)}
    for j, (w, n, e, s) in enumerate(ordered):
        value = w + 2**8 * n + 2**17 * e + 2**25 * s + 127 * 2**34
        coefficients[j] -= 2**10 * value
    control = [(10, 1023, 8), (18, 1013, 9), (27, 1003, 8), (35, 983, 9),
               (44, 1031, 1), (45, 1022, 1), (46, 1011, 1), (47, 992, 1),
               (48, 1095, 1), (49, 2195, 1), (50, 3296, 1)]
    for b, e, m in control:
        for j in range(m):
            coefficients[e + j] = coefficients.get(e + j, 0) + 2**(b + j)
    return coefficients


def reconstruct():
    power = lambda exponent: 1 << (67 * exponent)
    beta = power(8807) - 1
    support = set(range(943)) | set(range(983, 993)) | set(range(1003, 1012))
    support |= set(range(1013, 1032)) | {1063, 1064, 1095, 2195, 3296}
    mc = beta - sum(power(e) for e in support - {1}) - 2 * power(1063)
    mf = beta + 4 + (2**51 - 2) * (power(4393) + power(5495))
    mf += sum(power(e) for e in range(1013, 1023)) + sum(power(e) for e in range(1065, 1074))
    mf += power(2195) + power(3296)
    mf += (2**65 - 1) * sum(power(e) for e in range(8792, 8805)) + (2**19 - 1) * power(8805)
    phi = tile_coefficients(decoded_actions())
    k0 = sum(power(e) for e in (30, 62, 1100, 2201, 8849))
    k0 += sum(coef * (power(4393 - e) + power(5495 - e)) for e, coef in phi.items())
    values = dict(beta=beta, K0=k0, MC=mc, MF=mf)
    require(beta % 2 == 1 and beta >= 31 and k0 > 0 and 0 < mc < beta < mf < 2 * beta,
            "the uniform arithmetic port conditions")
    return values


def main():
    directory = HERE / "positive" / "coefficients_bfs"
    directory.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, value in reconstruct().items():
        filename, expected = EXPECTED[name]
        data = value.to_bytes((value.bit_length() + 7) // 8, "little")
        digest = hashlib.sha256(data).hexdigest()
        require(digest == expected, f"whole reconstructed payload {name}")
        target = directory / filename
        if target.exists():
            require(gzip.decompress(target.read_bytes()) == data, f"stored payload {name}")
        else:
            target.write_bytes(gzip.compress(data, mtime=0))
        records[name] = {"file": filename, "bits": value.bit_length(), "raw_sha256": digest,
                         "gzip_sha256": hashlib.sha256(target.read_bytes()).hexdigest()}
    receipt = {"seed_characters": len(SEED), "transitions": 430, "tiles": 943,
               "all_four_full_values_match_pinned_page": True, "ports": records}
    (directory / "RECONSTRUCTION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
