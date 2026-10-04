# Independent audit: prime-index free83 collapse

Verdict: **PASS; no unresolved mathematical defect found.**

Audit target: VladimirReshetnikov/ProveIt commit
`8cf6239b6d805b08f106c7fe31ea4b5b46601722`,
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/free_coefficient83_prime_outer_collapse.md`.
The accompanying mathematical review was read as a claim to check, not as a substitute for the audit.

## Result and Report46 scope

The unchanged inherited free-coefficient83 circuit has infinitely many full positive zeros at every positive ordinary input on every valid fixed-program slice. Its intended compiler representation is therefore refuted: it accepts all positive inputs even on the actual empty-language compiler slice. More generally it fails on every slice whose intended language is a proper subset of the positive integers. This is not a statement that it disagrees with an all-positive-input target language.

The new construction uses prime main indices `p = 1 (mod 4)`. Report46's nonextension theorem fixes even main indices and retains the five existing outer factors. Both results can hold, and do. The odd-prime construction replaces those retained outer witnesses. It does not extend the forbidden even-index family.

Recommended replacement for stale global open-soundness wording:

> The unchanged inherited free-coefficient83 circuit is now known to accept every positive ordinary input on every valid fixed-program slice, with infinitely many full positive witnesses. A separate odd-prime-index construction therefore refutes its intended compiler representation, including on the empty-language slice. The present even-index fixed-family nonextension remains valid. The sound84 upper bound is unchanged; other 83-operation circuits and other coefficient recipes are not excluded.

## Independently checked mathematical steps

1. **Literal source and outer domain.** The packet's 83 rows have the stated seven factors and final subtraction of the register named `A`, which is mathematical `Delta`. I checked the actual bound, input root, main root, index, transport, auxiliary and strong expressions against the proof. There are 18 strictly positive supplied witnesses, one ordinary input and six fixed numeral ports. The assignment `Z=w=transport_quotient=1`, `W=2^(2dx+b)`, `C=W+1`, `F=(K0+1)C` and sufficiently large `q=B^N` gives positive original slack and transport factor one. The shifted native/source MF distinction is retained. Its packing identity gives positive odd R and `R<=q^4-q^3+q-2`, hence `0<R+1<E=q^4s`. No toy mask is used as a compiler export.

2. **Reduced prime progression.** The compiler proof fixes d and b as powers of five and gives the required mask ranges and parity. With N another power of five, `Dwidth=dN` is odd and one modulo four, while `q=2^Dwidth` is two modulo five and minus one modulo three. Thus `Cprime=4q^3(q+1)/3` is integral and two modulo five. The progression `Cprime+1+5Cprime*t` is coprime to its difference. Dirichlet supplies a fixed prime `ell>3`, congruent to three modulo five. Then `H=3ell`, `L=2(ell-1)` is a return exponent for 2 modulo H, and five does not divide L. Therefore `p=Dwidth (mod 4L)` is reduced, gives `p=1 (mod 4)`, and forces `2^p=q (mod H)`.

3. **Positive input and main roots.** I rederived `E_A(v)=2^v+H*gamma_v` and its stated recurrence from the Pell recurrence. The recurrence makes gamma positive and increasing from v=2. Since u is odd and at least three, the binomial reduction gives `psi_A(u)=u (mod Delta)` and strict growth gives positive integral delta. Rho is positive. The input root is exactly positive `chi_A(u)`. For sufficiently late main primes, integral `gamma-rho` is positive, and the literal main root is positive `chi_A(p)`. Neither a negative root nor weakened outer slack is substituted.

4. **Prime ratio hits.** `A<P<2A^2-1`, the odd two-adic valuation of `P^2-1`, and odd Delta establish `1/2<theta<1` and irrational theta via distinct quadratic fields. The fixed reduced-progression theorem below applies to `theta/(E/2)`. The hit interval is strictly inside one unit cell because `n0=(R+1)/2` is an integer in `(0,E/2)` and `0<h_ratio<1`. Thus the floor n has exactly the required congruence. The pinned conjugate-error estimate works for the chosen arbitrary positive s: taking both errors below `1/[12(Y+1)]` preserves both strict inequalities. Eta and zeta are positive, and on a tail so is integral h. The actual first norm and index factor are one.

5. **Auxiliary CRT.** For odd prime `p>Delta`, Frobenius in `F_p[t]/(t^2-Delta)` gives `c=psi_A(p)=Delta^((p-1)/2)=+/-1 (mod p)`. Since c is odd, `gcd(c,8p)=1`. Set `f=chi_A(2p)` and `S=Delta*psi_A(2p)`. The CRT index `ell_aux=R (mod c)`, `ell_aux=3p (mod 8p)` exists and is three modulo four. The integer quotient polynomial gives `V=-R (mod c)` and, using the Pell-state return at 8p and `psi_A(3p)=(2f+1)c`, gives `V=-c (mod f)`. Also `f^2=1 (mod c)` and `gcd(c,f)=1`. Therefore the proposed T is integral and strictly positive. The actual auxiliary expression recovers V, its norm equals one, and the strong factor equals Delta. S is greater than one, and the auxiliary index is positive, so all auxiliary Pell coordinates have the required positive domain.

All 18 source witnesses are thereby positive integers, and the factor list is exactly `(1,1,1,1,1,1,Delta)`. The fixed paid finalizer vanishes. Distinct unbounded prime indices yield distinct c, hence infinitely many tuples. The nonintegral parent inverse is a separate consequence, not a premise for language failure.

## Independently opened analytic sources

- Caragea and Lee, *A note on exponential Riesz bases*, published 28 July 2022: https://link.springer.com/article/10.1007/s43670-022-00031-9 . The paragraph immediately before Proposition 7 and its d=1 case give qualitative uniform distribution of irrational multiples of primes.
- Bhakta, Loughran, Rydin Myerson and Nakahara, *The elliptic sieve and Brauer groups*, arXiv:2109.03746v3 (17 March 2023): https://arxiv.org/pdf/2109.03746 . I checked the finite residue filter in the proof of Lemma 3.16, printed pp. 13–14, and the progression prime count on printed p. 15. No elliptic-curve hypotheses or quantitative bounds are imported.

The progression extension is independently sufficient: for each nonzero Fourier index h, the residue indicator expresses the prime sum over `p=r (mod m)` as a finite average of all-prime sums at irrational frequencies `h*alpha+j/m`. Vinogradov and Weyl make each `o(pi(z))`. For fixed coprime r,m, the prime number theorem in arithmetic progressions gives `pi(z;m,r)~pi(z)/phi(m)`, so normalization by the progression's own prime count still tends to zero. Weyl then gives uniform distribution on that progression. Here q, s, H, m, the interval and every threshold are fixed before p varies. There is no unproved uniformity in a growing modulus.

## Provenance and finite evidence

`SOURCE_PINS.json` records 13 independently retrieved GitHub connector files with exact commit URLs, Git blob SHA1, SHA256 and byte counts. Every Git blob identity matches; all twelve SHA256 pins listed by the upstream review match. The fetched literal83 JSON also has the same SHA256 `682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016` as the separately recovered delivered Report43 source. Historical open-soundness metadata is retained byte-for-byte as historical evidence.

The newly authored `check_independent.py` passed under normal Python and `python -O`, with byte-identical receipts. It performs a static dependency/liveness walk only, not execution of saved source rows: 83 live rows, 25 live free ports, 46 multiplications and 37 additions/subtractions, 18 positive supplied witnesses. It separately checks 464 gamma states and 45 small exact main/strong/CRT cases; huge auxiliary coordinates are checked only via exact modular quotient arithmetic. No upstream Python, saved schedule, or predecessor verifier was executed.

Degree 111 is inherited from the identical frozen source certificate, not freshly expanded here. No full valid-compiler giant zero is materialized, and finite checks do not prove Dirichlet, prime equidistribution, or the infinite-existence conclusion. The argument audited above supplies that conclusion.
