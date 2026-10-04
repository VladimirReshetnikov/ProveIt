# Independent review of the native small-prime digit rules

PASS on the revised frozen packet. The genuine-history theorem is valid under the stated fixed compiler parity hypothesis, and the separate full-residue extension theorem has the required unrestricted-high-prefix qualification. One sentence initially asserted a geometric-sum congruence at too strong a modulus. It was corrected before this review was frozen; no stronger congruence is needed. No further finding remains.

## Frozen inputs and coverage

The reviewed author files are [the helper](complete83_gamma_small_prime_digit_rules.py), [the receipt](complete83_gamma_small_prime_digit_rules.json), and [the proof](complete83_gamma_small_prime_digit_rules.md):

| File | SHA-256 |
| --- | --- |
| PY | `98a5e098cf868e7dd6eac5d71a0d1d384d4eec87abec29eb813b8742180a6e22` |
| JSON | `8c074efc32c1bf5795e8f6f300a25491fa79969d6a08ffe98b28022354074ff3` |
| MD | `b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e` |

The revised MD supersedes `92b6fe38d92d302850c92c13b14eb768333d606bf9f4d979ff37387776f72127`. The helper and receipt did not change.

I read the entire author helper and proof, inspected the receipt schema and all certificate records through an independent evaluator, and authenticated all six dependencies:

| Dependency | SHA-256 |
| --- | --- |
| `complete83_gamma_native_finite_prime_avoidance.py` | `c13626a4efc17639f0b3d3ec59fb574c90c3a8af1cc51e2db7d73b20739b3e81` |
| `complete83_gamma_native_finite_prime_avoidance.json` | `1a4fd227072987420e6533195e5efa29dfc636d109ae8e5e08c61ebeedea8849` |
| `complete83_gamma_native_finite_prime_avoidance.md` | `93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96` |
| `complete75_half_binomial_compiler.md` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| `complete75_gamma87_compiler_order_filters.md` | `43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3` |
| `complete83_independent_gamma_scout.md` | `bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41` |

For predecessor context, I reread the entire finite-prime proof and compiler-order-filter note, and the modified compiler's fixed-mask, genuine-word completeness, and five-adic-control passages. The remaining full positive-converse obligations are inherited as explicitly cited by the author and by the [previous independent finite-prime review](review_complete83_gamma_native_finite_prime_avoidance.md). This is not a new execution or recertification of the historical compiler exporter. No predecessor Python was imported or executed.

## Actual compiler restrictions and the genuine-history theorem

The low-residue calculation uses the actual origin Start selector, not an independently supplied index: `Z=1`, `MC=-2`, `J=1`, and `q=0` modulo `2^b`, hence `R=-1 mod 2^b`. The selected dummy exponent is above the Start/End positions, so the permitted moves preserve this calculation. The pinned compiler-order proof retains the literal `MF+B-1` source offset and gives `R=MC mod 3` for canonical odd `N`. Thus the three parity classes and the displayed evaluation bases at 5, 7, 13, and 17 agree with the actual layout. In particular, even selector count and odd tile-alphabet size give `R=0 mod 3` independently of the dummy choices. No compiler-padding theorem removing this hypothesis has been used.

For this class, canonical alignment gives `E|R`, with `E=dh` a power of five. Consequently `3E|R`, and `R/(3E)` is odd. This strengthens the unconditional plus-factor argument to

```
2^(3E)+1 | a,
Delta = 3 mod (2^(3E)+1),
v3(2^(3E)+1)=2,
v3(Delta)=1.
```

The enlarged controller fixes `h`, then `Q=3(2^(3E)-1)` and its finite prime set, and only afterward enlarges `Htime`. The grid `i_j=6hj` returns modulo every required prime because `B^(6h)=2^(6E)=1` there. The inequality `Htime>5(6Q-11)` proves `i_max+h<N/5` and `i_max+4N/5+h<N`; it also covers the spatial shift by one. Source and destination upper bits are disjoint, lower bits remain independently available for five-adic alignment, and all dummy digits remain in `0..3`. The inherited exact valuation of `B^(4N/5)-1` preserves that alignment after every switch.

The corrected modulus step is precisely sufficient. Write `G=Gamma(B^(4N/5)-1)` and `s_p=v_p(G)`. One has only

```
sum_(j<k) B^(6hj) = k mod p,
```

but multiplication by `G` proves

```
r_k = r_base-G*k mod p^(s_p+1).
```

The digit at position `s_p` therefore ranges bijectively with `k mod p`. CRT gives a single `k<rad(Q)<=Q`, within the available prefixes, forcing a digit `p-1` at every selected prime. A carry into such a digit does not invalidate the central-binomial divisibility; a carry in the doubling exists in either case. The argument never requires the unweighted sum to equal `k` modulo `p^(s_p+1)`.

For a prime dividing `2^(3E)-1`, the actual `3E|R` fixes the evaluation base at 1. Central divisibility then yields `a=1/4` and `Delta=65/16` in that prime field. The only possible odd prime divisors of 65 are 5 and 13, whose orders 4 and 12 cannot divide the odd number `3E`. Thus the minus factor is coprime to Delta. The two neighboring odd factors are coprime, so

```
gcd(Delta,2^(6E)-1)=3.
```

The composite has exact 3-adic valuation 2. Division by 9, not by 3, removes its full 3-part and gives the claimed coprime quotient. Since `m|2Delta`, the same quotient is coprime to `m`, and `v3(m)<=1` follows. The exclusion of 7 is genuine in this compiler parity class; it does not follow in the other two classes from the same symmetry argument.

The source-side conclusion uses fresh positive witnesses at the modified actual index. The inherited digitwise `2C+F<q/2`, unchanged Start/End, positive slack, population, and temporal congruence are unaffected by how many allowed upper bits move. The old numerical Pell tuple is not retained. The finite-prime construction supplies a genuine accepting history before applying the established positive converse and the independent-gamma forward chart. It does not presume soundness of the 83-operation chart.

## Digit recurrence and its quantifiers

The two Lucas-split formulas follow by separating the high row index from its low digit. When `2d>=p`, the low row length `2d-p` is below the threshold digit `d`, forcing the high row index to be at least `k+1`; Pascal's identity gives the stated second formula. These formulas also handle `x=-1`. The normalized-state argument separately requires `x!=-1`, as the author states.

For that argument, the coefficient of the prior upper-tail sum in either branch is `z^d`, where `z=(1+x)^2/x`. Once the high prefix has zero central coefficient, arbitrary appended lower digits preserve both that zero and `T(r)=z^(-r)G(r)`. This is a high-to-low statement and does not claim that an arbitrary replacement of the high prefix preserves a previously computed state.

All seven rows of 75 finite certificates cover every value of `T` in the respective field. Given `M` coprime to `p` and divisible by `p-1`, a compatible phase, and a low suffix modulo `p^ell`, the CRT suffix lies below `M*p^ell<=p^L`. It therefore leaves the chosen high prefix intact. The phase fixes both `z^r` and `2^(2r+1)`, while prefix selection supplies any desired residue of `a`. Every saved prefix is positive, so letting `L` grow gives infinitely many indices. Finite intermediate digit prescriptions are included by completing them to one low residue; compatibility with the scalar congruences remains necessary.

This theorem deliberately permits unbounded higher digits. It does not retain a fixed packing range, population, masks, convolution, or computation, and it does not realize its generic residue extensions as histories. Thus it limits a scalar-congruence/finite-digit argument without excluding a proof that uses the omitted history constraints.

## Fresh checks and limits

Fresh normal and optimized author receipt replays from `/` passed against the frozen JSON and all six dependency pins. The helper uses explicit exceptions, and its duplicate/nonfinite JSON rejection and recursive type comparison remain enabled under `-O`.

A separate fresh evaluator read only the saved JSON. It used a most-significant-digit Lucas equal/greater comparison over the full weighted binomial row, rather than the author's recurrence. It independently verified all 75 carry-prefix records, all 75 synthetic congruence extensions, and all 127 seven-formula records: 277 weighted-row checks. It also checked the three actual phase rows and 255 weighted geometric-sum congruences supporting the corrected modulus step. All passed.

The author's finite evidence counts are accurate: 4,598 recurrence comparisons, 919 append checks, 75 prefix certificates, 75 synthetic extensions, 127 seven-formula samples, two grid geometries, 27 synthetic digit targets, three prime/order examples, and two factorizations. These are finite formula, congruence, and geometry checks. Neither this review nor the author helper materializes a full accepting history or giant positive Pell tuple.

No new paid source, universal operation bound, full bound on `m`, infinite-prime avoidance history, rejected-input alias, or resolution of the independent-gamma83 language follows. The genuine theorem retains its compiler parity hypothesis, and the unrestricted digit theorem retains its non-history scope.
