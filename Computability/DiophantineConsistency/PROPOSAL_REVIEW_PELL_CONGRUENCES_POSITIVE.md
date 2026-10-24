# Pell congruences: positive companions

The eleven-positive companion is a valid ordinary-mathematical improvement to **111 live binary operations, exact degree 269**. The twelve-positive companion is also supported, at **102 operations, degree 78**, but our materialized [ordinary 100/70 equation](research/ordinary-unit-products/README.md) is smaller on both measures. No Lean work was performed: formalization remains paused.

The reviewed arrival is `eae4f1952b`, archive `con_zfc_pell_congruences_2026-10-23.zip`, SHA256 `7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a`. Its full 230-file extraction was reviewed in scratch. All 229 manifest hashes pass, and the original tree remains unchanged. Detailed receipts are in [the review JSON](data/pell-congruences-positive-review.json). The root agent reviews its nine-positive companion; the integer transport companions are reviewed separately.

## Exact comparison

| Positive unknowns | Binary operations | Exact degree | Assessment |
|---:|---:|---:|---|
| 11 | 111 | 269 | New useful point; improves 111/277 and 113/325 |
| 11 | 114 | 257 | Remains a degree/cost tradeoff before the separate polynomial-shears review |
| 12 | 102 | 78 | Correct, dominated by our 100/70 |
| 12 | 100 | 70 | Existing ordinary-norm candidate remains preferred |

The eleven-variable graph has 65 multiplications, 29 additions and 17 subtractions. The twelve-variable graph has 57 multiplications, 26 additions and 19 subtractions. Every gate, unknown and fixed port is live. Both use the **entire compact44 tuple**, with `beta=2^590069-1` and the already shifted `MF_source`; the four actual numeral payloads were reconstructed and independently authenticated. No tuple components are mixed.

## Proof review

The new source is the normalized positive Pell interface. Its first carrier restores `q³|Y`, the transport divisibility and `C>0`. The main carrier supplies a positive integral main Pell root. These steps precede strong/auxiliary index recovery. First/main Pell classification excludes first index one, giving `c>8XY³>=8q⁹>2R` and `c>2p`; neither estimate assumes the desired exact index `p=R` or the still-deleted divisibility `q|X`.

The lower main modulus `U=q²Y`, with `S=qY`, is justified by an exact cofactor argument. Since `J=1 mod 3`, compact44's `beta=1 mod 3`, and `q³|Y`, one has `gcd(q,H)=1` and `gcd(H,U)=gcd(3,Y)=g` in `{1,3}`. Crucially, `gcd(g,q)=1` means `q³|(Y/g)`. Thus `mu=qY/g>=q⁴>R`; estimating only `qY/3` would be insufficient. After the inherited signed auxiliary-index lemma gives `p=R`, this modulus forces `2n0=R+1`. Only then are `U|k-R-1`, `q|X`, and the positive old index/main quotients restored. The order avoids a circular scale assumption.

The rational saturation lemma is sound: from `QV²-(Q-1)y²=1` with integral `Q>1,V` and rational `y=a/m` in lowest terms, one gets `m²|Q-1`. The norm-preserving descent has integral first coordinate and preserves the reduced denominator of the second. Its nonzero absolute first coordinate strictly decreases until it is one, forcing `m=1`. Adjacency of `Q,Q-1` is essential; this does not assert integrality for arbitrary rational Pell points.

For eleven variables, the octic norm eliminates the first root, strong root and auxiliary ordinate. Its positive rational radicands are distinct. The text proves the exceptional signed sum cannot vanish: when `cT-R=0`, the strong root dominates the other two; otherwise the auxiliary root dominates. A nonzero rational sum of three signed roots of distinct positive rational numbers makes all three roots rational by the displayed symmetric identities. The first two are integral because their squares are integers; the third becomes integral by the saturation lemma. Thus removing the old `q(q-1)` factor from `I=i c²` is justified.

The separate transport multiplier is the key size change: `L=3Df(cT+Rhat)` bounds the two eliminated roots, while `h=Df*cT` enters `W=1+(q-1)h`. Soundness needs only `h>0`. Canonical completeness has `Rhat<2q⁴<c<=cT`, hence `L<6h`, and the first carrier gives `r>qW-2k>6h>L`. Consequently `n=r-L+f+y>0`. The proof does not assume that an arbitrary old solution has this slack; it explicitly reselects canonical source witnesses.

For twelve variables, the first/main bounds already give `c>2R`, so `f=t+1>=2` and `T>=1` imply `V>c>1` before the merged norm is used. Its extraction denominator is therefore nonzero. The exact norm identity first gives a rational strong multiplier and auxiliary ordinate, then saturation makes the ordinate, gap and multiplier integral. Their absolute values restore positive source witnesses. The converse uses `n=i+u>0`; the `f=t+1` shift excludes the genuine `rho=0` degeneracy.

Both product finalizers are exact. In the eleven-variable two-factor case, `N8` is a square modulo four, excluding `N8=-2`; this alone rules out the pair of negative units, so an extra parity assumption on the main residual is unnecessary. In the twelve-variable case all three residuals are squares modulo four, because `q` is even and the merger tail has an explicit factor four.

No defect was found in these ordinary arguments. The universal compiler/refutation calibration and named signed Pell classification remain inherited mathematical dependencies. These checks are not a new Lean theorem or an internal-ZFC derivation of those dependencies.

## Finite replay and a release-driver defect

The full positive replay passed normally: 44 upstream source identities, all four actual coefficients, independent native reconstruction, and both byte-identical circuit rebuilds. The exact independent verifiers also passed directly under `python -O`. Their identities include both carrier cancellations, the three-root norm, rational extraction, the saturated merger, its factorization and the descent norm. Exact leaders give nonzero coefficients `8(3 beta)^36` at degree 269 and `64(6 beta)^18` at degree 78, independent of the other fixed ports.

The advertised bare `python -O positive/verify.py` **fails as delivered**: its children run as `[sys.executable, script]`, which drops the parent's `-O` flag. It then reads `AUDIT12_OPTIMIZED.json`, although its normal child created `AUDIT12.json`. This is a packaging failure, not a failed identity. With the inherited environment `PYTHONOPTIMIZE=1`, the unchanged full driver passes under `-O`; all spawned builders, coefficient programs and algebra checkers then run optimized too. Both outcomes are retained in the receipt. No delivered source was patched.

No further cross-composed endpoint is claimed. Replacing the eleven-variable normalized strong root by an ordinary root is not a substitution licensed by the saturation lemma alone: its radical scaling, nonzero extraction and signed-index hypotheses would need a separate complete proof and live circuit/degree certificate.
