# Independent review: beta=47 q=48 toy

The toy seed has R=219127, X=2^R≡32 mod 48, the stated positive guard, and the stated scalar window. The independent modular sum tracks each binomial coefficient by its 3-adic valuation and unit modulo 27, obtaining numerator 0 modulo 27 without constructing Y. Legendre's formula gives central-term valuation 12; all noncentral half-terms are divisible by 2^(R−1), so v₂(Y)=12. Consequently 48³=2¹²·27 divides Y, and U=Yq² divides m=XY² even though 48 does not divide X. The aligned-index Pell completion is the separately reviewed symbolic construction; its enormous witnesses are not expanded.

The parent exclusion is conditional on the required source index/trace replay and applies only at q=48. These are not the compact44 ports, and no Lean theorem or PDF binding is asserted. Run `python3 -I -S -B check.py` and compare with `result.json`.
