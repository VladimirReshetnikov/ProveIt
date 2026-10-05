# Gamma83: a native carry obstruction to the quartic two-prime target

On the existing simultaneous7/31 filtered histories, the proposed target

```
H=3[p(10p-9)]^f
```

is impossible for **every positive exponent f**, even before requiring the two factors to be prime. More generally, that genuine subclass excludes all factor shapes `p(kp-k+1)` with `k=1,3,5 mod7`. A separate observation supplied by root excludes every `3|k` in the sufficient quartic pair family, already on the original finite-prime filtered subclass.

Before imposing the mod7 filter, the k=10 target requires an all-size digit restriction: on any31-filtered canonical history with3|R, every base7 digit of r=(R-1)/2 must be at most3. For prime pairs there is an additional exact digit-count residue table. These results narrow a proposed sufficient route; they do not prove that the independent-gamma83 language is sound, bound every alias period, or exhibit a false input.

## 1. Exact inherited native domains

Keep the unchanged independent-gamma83 source and a genuine canonical accepting history of its parent. Its actual parameter is

```
R=2r+1, X=2^R, C_R=binom(2r,r),
G_r(T)=sum_(j=0)^r binom(2r,r+j) T^j,
2Y=G_r(X), a=Y(X+1), H=4a+3,
q=2^t>=16, popcount(R)=3t+2.
```

C_R in this note is the central binomial coefficient, not the compiler content word. No independent value of H, Y or R is inserted. The previously established native formula gives `v2(a)=3t`, and6 divides a.

The original finite-prime construction fixes the compiler and an adequate spatial padding h first, with E=dh a power of five and5|E. At each accepted ordinary input it constructs genuine histories with

```
5|R, 31|C_R, H=4 mod31, H/3=22 mod31,
a=0 mod9, v3(H)=v3(Delta)=1.
```

The order of22 modulo31 is exactly30: its powers at30,15,10,6 are respectively1,-1,5,8. Thus for **any** representation

```
H=3u^f, u an integer, f>=1,                         (1)
```

u is a unit modulo31. If s=ord_31(u), the equality `30=s/gcd(s,f)` and s|30 force

```
ord_31(u)=30, gcd(f,30)=1.                          (2)
```

In particular f is odd and prime to3. This applies to general u, not only prime or two-prime complements. It is not the older k=2-specific restriction `f=13,17,23,29 mod30`.

The stronger native small-prime theorem has explicit fixed-compiler hypotheses: an **even window-selector count k_win and an odd tile-alphabet size**. On that class every canonical R is0 modulo3. Its allowed ignored-bit construction can impose simultaneous central carries at every prime of `2^(3E)-1`, including both7 and31, while preserving the actual accepting word, ordinary input, masks, packing, population and positive-witness converse. Thus at each accepted input it supplies genuine histories with

```
3E|R, 7|C_R, 31|C_R,
H=4 mod7, H=4 mod31, a=0 mod9.                     (3)
```

The full construction and positive completion are inherited from that proof, not reconstructed by numerical samples here. The parity-padding note supplies this compiler parity for a new representation of every c.e. language, but **changes the fixed compiler numerals**. It does not impose the parity on a previously fixed coefficient instance. We keep that distinction throughout.

## 2. All exponents are excluded for k=10 on the stronger subclass

**Theorem 1.** If an actual history satisfies H=4 modulo7 and H=4 modulo31, then it has no representation

```
H=3[p(10p-9)]^f,
p an integer, f>=1.                               (4)
```

Proof. Put u=p(10p-9). Equation(2) holds, so gcd(f,6)=1. At7, (4) gives `u^f=4/3=6=-1`. Raising to the inverse of f modulo6 shows u=-1 modulo7. Equivalently, because the f-th power map is a bijection of the six units and f is odd, -1 has unique preimage -1. But u=p(3p-2) modulo7, so

```
3p^2-2p+1=0 mod7.
```

Its discriminant is `4-12=-8=6 mod7`, while the square residues are0,1,2,4. This is impossible. No bound on f, primality claim, numerical factorization or source evaluation is used.

Consequently every history supplied by (3) excludes the target. This does not exclude it on every canonical history or on the original mod31-only subclass. Nor does it disprove the quartic sufficient criterion: a different numerical factorization or the factorization-free power test might still succeed at the same H.

Both residues have a purpose. Without the31 restriction, odd f alone would not invert the power map at7: for example p=4 modulo7 gives u=5 and u^3=-1. This is only a local counterexample to dropping the exponent premise, not a native history. Conversely, without3|R and the central carry, the actual base X need not be1 modulo7 and the conclusion H=4 does not follow.

**Review remark 1 (retained k=10 proposal).** The frozen quartic note, Section4, calls

> The useful new exponent-one target is

and then displays `u=p(10p-9), P=10p-9 prime, p prime>3, p=2 or3 mod5`. Its statement that there is no **mod31** obstruction at f=1 is correct: it gives p=2 modulo31, compatible with the separately recorded dyadic condition. The stronger conclusion suggested by treating that compatibility as a viable target on the **simultaneous7/31 subclass** is now refuted by Theorem1, for all f. The frozen note remains unchanged; the exact proposal and the new counterevidence are retained here. No occurrence was claimed in that note, and its arithmetic certificate proofs are not retracted.

## 3. A general factor-parameter restriction

**Theorem 2.** Under the same two native residues as Theorem1, a representation

```
H=3[p(kp-k+1)]^f, k and p integers, f>=1,
```

requires `k=0,2,4,6 mod7`.

As above, the complement must be-1 modulo7. If k is nonzero modulo7, its quadratic equation has discriminant

```
(k-1)^2-4k=k^2-6k+1=k^2+k+1 mod7.
```

The entire field calculation is:

| k mod7 | Discriminant mod7 | Required p mod7 |
|---:|---:|---|
|0|1|6, from the linear equation p=-1|
|1|3|none|
|2|0|2|
|3|6|none|
|4|0|3|
|5|3|none|
|6|1|4 or5|

This proves the stated exclusion for all integers, not just prime pairs. The permitted rows are only the exact solutions of this one local equation; they are not sufficient for a native factorization, primality or all other congruences. The factor parameter k is unrelated to the compiler selector count k_win.

The following complementary restriction is credited to root's independent derivation.

**Theorem 3.** Suppose a is divisible by9, f is odd, and an actual H has the sufficient quartic pair form

```
H=3(pP)^f, p,P primes>3,
P=k(p-1)+1, k>=2, k|(p+1)(p^2+1).
```

Then3 does not divide k.

If3|k, p^2+1 is2 modulo3 and hence p+1 must vanish modulo3. Thus p=-1, P=1 and u=pP=-1 modulo3. Since f is odd, u^f=-1. But `H/3=1+4a/3=1 mod3`, a contradiction. This uses neither the new7 filter nor the mod7 table. The original finite-prime construction already gives a=0 modulo9; its31 residue supplies odd f. The stronger parity-normalized class supplies these hypotheses as well.

Combining the two theorems, any sufficient quartic prime-pair target on the stronger class must satisfy `3∤k` and `k=0,2,4,6 mod7`. No claim is made that these necessary restrictions exhaust the native obstructions. Root's preliminary k=30 exploration and its retraction are recorded separately in the root review; it is already excluded by Theorem3.

## 4. Before the7 filter: an exact carry and digit-count obstruction

The next result does not assume7 divides C_R. Assume only an actual canonical history with3|R and the31 residue of Section1. Then X=1 modulo7, and binomial symmetry gives

```
G_r(1)=(2^(2r)+C_R)/2,
a=(X+1)G_r(X)/2=1/4+C_R/2 mod7,
H=4+2C_R mod7.                                    (5)
```

If the k=10 target holds and7 divides C_R, (5) supplies the two residues of Theorem1, a contradiction. Therefore that target forces `C_R!=0 mod7`. Equivalently:

```
every base7 digit of r=(R-1)/2 lies in {0,1,2,3}.   (6)
```

To justify the equivalence for every r, the factorial valuation identity counts carries in r+r in base7. If every digit is at most3, no carry starts. If a digit is at least4, the first such digit creates a carry, so7 divides the central coefficient. The same conclusion follows from the first low digit at which Lucas's numerator digit becomes smaller than its denominator digit.

When (6) holds, let N_j count the digits equal to j. The digitwise binomial identity, with coefficients `binom(2j,j)=1,2,6,20` for j=0,1,2,3, gives

```
C_R=(-1)^(N_2+N_3)*2^N_1 mod7.                   (7)
```

For prime-pair targets the residue restriction can be sharpened. Here p>3 and P=10p-9 are prime. Equation(2) makes f odd. Since `H/3-1=4a/3` has exact2-adic valuation3t+2, odd-power factorization gives

```
v2(u-1)=3t+2,
u-1=(p-1)(10p+1),
v2(p-1)=3t+2.
```

Thus p>7 and P>7. Their residues exclude p=0 or3 modulo7; the latter would make P=0. For the remaining residues:

| p mod7 | u=p(10p-9) mod7 |
|---:|---:|
|1 or2|1|
|4 or6|5|
|5|2|

Equation(2) leaves f=1 or5 modulo6. Solving `4+2C_R=3u^f` gives the exact necessary table

| f mod6 | Allowed C_R mod7 |
|---:|---|
|1|1,2,3|
|5|3,4,6|

Together with (6)–(7), this is a finite digit-count test on the actual index. A carry, or a forbidden value of (7), excludes the target for that genuine history without factoring H or constructing the large Pell coordinates. The proof does not assert that all permitted digit words are compiler histories, that the remaining digit class occurs at any accepted input, or that the test decides the full gamma83 language.

The old31² screen remains a separate necessary condition at f=1 on histories not already excluded here. Passing it cannot repair a failed7 carry condition. No iteration of local tests is asserted to be a complete test for numerical factorization.

## 5. Source pins, scope and new finite evidence

All dependencies are in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` and were authenticated as inert bytes.

| File | SHA256 |
|---|---|
| gamma83_quartic_complement.md | 135edefc6b53e0d55350f74a7fe1186eda3c59046f0098128bbef4796fcd6d9c |
| gamma83_composite_complement_certificate.md | 70d5311c481545f0dc1655dff54040b7badc3802a6e621d284c39c5751a8c255 |
| gamma83_native_next.md | 6cf4719fab43ad8873e372a5be0108192cc0a90cadccd84fe58d1e7a76cdaf74 |
| complete83_gamma_small_prime_digit_rules.md | b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e |
| gamma_parity_padding_scout.md | 0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c |
| complete83_gamma_native_finite_prime_avoidance.md | 93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96 |
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 |

The quartic and parity-padding notes were reread in full in this continuation. The full composite-complement, native-next, small-prime and original finite-prime proofs were read in the preceding continuation and their specific domain/carry conclusions checked again here. The prime-scaling and ternary-exclusion notes were also read in full as comparison context. Their formula-only examples are not promoted to compiler histories. The actual83 JSON is hash-bound only: there is no new row audit or circuit interpretation.

The new helper reads dependencies only as bytes. Fresh finite evidence checks the exact order30 certificate at31, all392 `(k mod7,p mod7,f mod30)` cases with gcd(f,30)=1, the three odd-exponent residue classes in the ternary obstruction, the complete prime-unit digit table, all2048 central coefficients for0<=r<2048 against (6)–(7), and17 direct native-formula residues at `15<=R<1000`, R=15 modulo60. Those small indices are formula checks, not instantiated compiler histories or full positive zeros. The unrestricted conclusions are the proofs above, not extrapolations from these cases.

Fresh normal and optimized exact receipt checks from `/` passed before freeze. Helper SHA256: `942d4154711cb4263b0bd99eea7e7f11b656497a36e355b155e3c06f4bcd93b7`. Receipt SHA256: `ea905275d88181ce11ec7fb1f9fbf982e29c06cfdcad27b49edd68d63d84d8c1`.

No supplied, archived, committed, frozen or copied predecessor helper/source array ran or was imported; only the fresh author corroborator ran before freeze. No repository or Git object changed. There is no new arithmetic circuit, gate saving or gamma83 language conclusion.
