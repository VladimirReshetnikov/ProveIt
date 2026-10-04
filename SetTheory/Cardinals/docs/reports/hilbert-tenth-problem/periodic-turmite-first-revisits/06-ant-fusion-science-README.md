# Fused background polynomial candidate

This separate research candidate fuses Report47's structured coefficient grammar
with Report44's two spatial initializer Horner expressions. It does not modify
any frozen report or release. No upstream ant/color/physical program or saved
schedule is executed, and no giant coefficient integer is instantiated.

## Result (author-verified; independent audit requested)

| Source | M | A (including subtraction) | Total |
|---|---:|---:|---:|
| Two raw inputs | 5,971,120 | 8,687,814 | 14,658,934 |
| One raw input | 5,971,124 | 8,687,820 | 14,658,944 |

Both constructions have literal leaves only1/3, the original465/467 positive
witnesses, one final equation, exact degree2,304,000, and the **same complete final
polynomial** as the frozen Report44/47 source. This is not merely a zero-set
equivalence or an ant-dynamics claim.

Compared with Report47's31,388,831/31,388,841 gates, the specified new grammar
saves16,729,897 gates, approximately53.299% in the two-input case. This is a count
of two specified grammars, not an optimality or novelty-priority claim.

## Exact ledger

| Stage | M | A | Total |
|---|---:|---:|---:|
| Unchanged occurrence constants | 5,469,985 | 8,186,999 | 13,656,984 |
| Small profiles/basic literals | 324,462 | 324,464 | 648,926 |
| G and five fixed ternary shifts | 283 | 45 | 328 |
| All584 anchor rows | 128,480 | 128,480 | 256,960 |
| Remaining named constants | 163 | 5 | 168 |
| Prefix subtotal | 5,923,373 | 8,639,993 | 14,563,366 |
| W^600 | 12 | 0 | 12 |
| Twelve short correction Horner factors | 7,188 | 7,188 | 14,376 |
| Twenty-four rotated occurrence factors/products | 23,040 | 23,038 | 46,078 |
| Fixed blocks and geometric weights | 15,911 | 15,714 | 31,625 |
| Fused Tile assembly | 8 | 8 | 16 |
| Fusion subtotal | 46,159 | 45,948 | 92,107 |
| All other two-input main gates | 1,588 | 1,873 | 3,461 |
| Complete two-input source | 5,971,120 | 8,687,814 | 14,658,934 |

The one-input main remainder has4 additional multiplications and6 additional
additions/subtractions. The original2,303,996 dense tile/first Horner gates are
removed only after their complete canonical recurrences are checked. All other
main gates, including anchors' spatial Horner evaluation and the sum-of-squares
finalizer, remain paid.

## Files and reproduction

- `PROOF.md`: ordinary-polynomial correction, block, Tile and full-source identities
- `fusion_source.py`: literal source generator and complete-source adapter
- `fused-receipt.json`: actual streaming counts/hashes/domain checks and finite array certificates
- `checks.py`, `checks-receipt.json`: exact exponent/array checks and dense modular differential cases
- `INPUT_PINS.json`: origin and hash of every authenticated local input copy
- `owned_report44/`, `owned_report47/`: inspected own-code arithmetic generators only
- `data/`: fixed JSON/mask data, not executable upstream programs

Run with assertions enabled and new output paths:

    PYTHONDONTWRITEBYTECODE=1 python -B fusion_source.py --out new-fused-receipt.json
    PYTHONDONTWRITEBYTECODE=1 python -B checks.py --out new-checks-receipt.json

The checks use the pinned `fused-receipt.json` for the finite block certificate.
Generation hashes the actual complete source but deliberately avoids retaining
the roughly14.7-million-record stream or evaluating its enormous constants.

Complete source SHA256:

- Two inputs: `62cf59e79cd5d3baf61b19ed50ccc8965e8fb4814bbdc33a6d7fad417d379667`
- One input: `722340689ce84f505af7d010db21d6b48178c5d6008b28966e9836aeca75b25b`

Final equations are gate14,658,933=gate0 and gate14,658,943=gate0, respectively.
Gate0 is the paid expression1−1. All canonical old-main hashes and positive
witness-name digests are checked and reported.

The author checks exhaust all2,296,800 correction exponent identities and all
6,912,000 fixed mask entries in both phases. Seven differential evaluations use
independent synthetic T values over small finite fields, including W=0,+1,−1,
and characteristics2/3. The algebraic proof, rather than modular testing, establishes
equality for all integer W and for the actual inherited occurrence constants.
