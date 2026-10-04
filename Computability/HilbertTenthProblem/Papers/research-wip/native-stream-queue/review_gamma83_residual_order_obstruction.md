# Independent review of the residual-order obstruction

**PASS, with no requested author change.** I read the complete frozen author helper and note, checked the exact cyclotomic/CRT proof and fixed-child-fiber statement, inspected the saved83 source's relevant consumers as inert JSON, independently reconstructed all six materialized CRT hosts, and replayed the new helper normally and with `-O` from `/`. Both exact receipt replays passed. No predecessor helper, compiler or archived code was executed or imported.

The reviewed author files are:

| File | SHA256 |
| --- | --- |
| `gamma83_residual_order_obstruction.py` | `d8ff9e4b457710b446eb5591ca88a5f4a5238b29339f1e1f71fc407831e8531c` |
| `gamma83_residual_order_obstruction.json` | `a98edefabc2ef0bd9e04ed8077ec21da6ce63a3016b11c61a2319ef6648fdb18` |
| `gamma83_residual_order_obstruction.md` | `7d2d15ccb608f295a344000f23d147b8f7ce2975e5732f2f6e2adc05363b2754` |

This review uses the corrected final note, whose exact identity is `16Delta=(H+1)(H+9)=(4a+4)(4a+12)`. It does not endorse the superseded draft containing the incorrect expansion.

## 1. Fixed full-zero fibers

The input criterion inherited from [the frozen83 scout](complete83_independent_gamma_scout.md) applies to every positive full child zero, with its native bounds and parities. It is not limited to forward images of parent zeros. In the actual83 array, alpha and x first enter `C_after_alpha` and `scaled_t`, which feed `marked_rhs` and the input index; the only direct rho/delta consumers are the input-root multiples. The shear

```
alpha_x=alpha_0+2d(x0-x)>0
```

preserves `marked_rhs=C` and `W=C-Z`. Refreshing rho and delta cannot change any of the six noninput factors. This agrees with the pinned scout's exact factor and outer-value proof; this review does not claim a new complete83 polynomial expansion.

For a full child zero, Delta is odd, A=a+2 is even, and H is odd and divisible by3. Thus `g=gcd(2Delta,ord_H(2))=2s` for odd s dividing Delta. Since `A^2-Delta=1`, A is coprime to s. The odd input-index branch requires `g|2d(x-x0)`; the even branch requires `g|2Ad(x-x0)`. Dividing each by2 and cancelling A modulo s proves their identical spacing modulus `m=g/gcd(g,2d)`.

The parity of the same discrete logarithm j is fixed by W modulo3, so this comparison does not create a second simultaneous progression on a fixed fiber. The inherited positive CRT completion supplies rho and delta only after the compatibility and positive-alpha conditions hold. The finite width is therefore retained. No parent soundness or positive gamma-minus-rho inverse is presumed.

## 2. Unbounded certified order divisors

For every k>=1, put `T=2^(17^(k-1))` and `Z=1+T+...+T^16`. The integer Z is odd and greater than1. Modulo17, `17^(k-1)=1 mod8`, hence T=2 and Z=1. Any prime divisor r of Z is therefore odd and different from17.

The identity `(T-1)Z=2^(17^k)-1` shows that `ord_r(2)` divides the prime power `17^k`. If it were a proper divisor, it would divide `17^(k-1)`, giving T=1 and Z=17 modulo r, contrary to r!=17. This proves the exact order without a primitive-divisor or prime-distribution theorem. A prime divisor always exists because Z>1; no effective factoring bound is asserted.

With n=3^u E and E a power of five, the moduli `2^n+1`, `2^n-1`, `17^k`, r, and `2^(3t+1)` are pairwise coprime. In particular:

* The two odd neighboring powers differ by2 and hence are coprime.
* The order of2 modulo17 is8, which cannot divide2n because n is odd.
* If r divided either power factor, its order `17^k` would divide `2n=2*3^u*E`, impossible.
* The remaining exclusions follow from r!=17 and oddness.

Therefore the five displayed CRT requirements have an infinite positive arithmetic progression of solutions. The two-adic congruence forces exactly `v2(a)=3t`, not just a lower bound. The first two congruences imply all the stated composite discriminant filters: on the minus factor, `16Delta=65`, and primes5 and13 are excluded there by their orders4 and12; on the plus factor, Delta=3 and its whole3-part has valuation u+1. The resulting `v3(Delta)=v3(H)=1` and `gcd(H,Delta)=gcd(H,9)=3` are consistent.

The conditions `a=-1 mod17^k` and `r|H` force `17^k|Delta` and `17^k|ord_H(2)`. Hence `17^k|g`, and division by the part shared with2d cannot remove it because d is a power of five. This proves an unbounded divisor of m at fixed d,E,t,u. It does not require computation of the whole order or of m.

Finally `H-1=-2` and `H-3=-4` modulo17^k. Multiplication by any power of2 cannot introduce a factor17. Reduction modulo the prime r therefore rules out both proposed power congruences for **every** squaring exponent e. The finite residue lists are supplementary evidence, not the proof of the all-e assertion.

## 3. Independent finite checks and scope

The author helper is a compact standard-library checker. Its eight inert pins match the source/proof dependencies named in the note; it reads the actual83 JSON, checks83 rows, and computes source dependencies to confirm that rho and delta occur in the input factor alone. Trial division proves the two recorded primes, and the two modular-power comparisons certify their exact prime-power orders. Its CRT, valuation and gcd checks use explicit exceptions and recursive type-exact receipt comparison. The author expressly disclaims an adversarial JSON-parser guarantee; no stronger parser certification is inferred here.

In addition to both author replays, I independently reconstructed each saved least nonnegative CRT solution using the idempotent formula

```
e_i=M/modulus_i,
a=sum_i residue_i*e_i*(e_i^(-1) mod modulus_i) mod M,
```

with M the product of all five moduli. All six values and CRT moduli agree exactly with the receipt. The saved a values have bit lengths 425, 446, 487, 502, 667 and 686. I recomputed H, Delta, the corrected discriminant identity, both certified divisibilities, and the coprimalities which prove the all-e obstruction. These checks did not factor H or compute its full multiplicative order.

The mathematical boundary is essential and is accurately stated by the author. These are **free arithmetic hosts**. They do not satisfy an asserted native half-binomial formula, packed-index population or masks, accepting computation, input-Pell component, or full83 polynomial zero. In particular the unbounded family at fixed t deliberately does not preserve the finite native range for R and a.

The separate genuine-history [three-power theorem](complete83_gamma_native_three_power_control.md), whose frozen note has SHA256 `addac036d27190fcf61632df3e0a632815f1e039efd6b96dd3d778005f83e448`, supplies the composite filter for each fixed u>=2 on selected histories. The obstruction here satisfies even stronger free residue conditions for every fixed u but omits the native formula. These statements are compatible. This review does not infer that the free hosts are realizable by that construction, or that actual native m is unbounded on any specified family.

The established conclusion is precisely that the listed extracted filters and elementary parity/valuation constraints alone do not bound m or force the old power tests. Neither ordinary-input soundness nor a false-input zero follows. No new operation bound is claimed.
