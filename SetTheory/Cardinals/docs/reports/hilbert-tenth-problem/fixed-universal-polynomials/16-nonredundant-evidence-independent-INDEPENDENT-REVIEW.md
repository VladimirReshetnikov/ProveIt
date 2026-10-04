# Independent review: the unwrapped fixed-lattice family

Date: 3 October 2026

## Verdict

**The reduced-predicate theorem is valid under the fixed-compiler and bootstrap premises retained by sealed Research Report 37.** I found no mathematical obstruction in the proposed construction. In particular, the curvature argument does support a shrinking target of width proportional to `1/log r`; this is stronger than qualitative equidistribution and is sufficient for the exact Pell ratio. The outer congruences, all strict predicate bounds, all positive supplied coordinates, and the two asserted one-residual sum-of-squares identities check out.

This verdict does **not** establish a solution of the omitted main congruence, an example with a nonzero main residue, logical independence of that congruence, or a sign theorem for the complete polynomial. The existence claim concerns infinitely many solutions of the predicate with that congruence deleted. The new family is conditional on the same source/compiler and auxiliary premises as Report 37; it does not independently reprove the universal compiler theorem.

No change to the theorem is required. The final clarifications resolve the two presentation points raised during review: the introduction now expressly disclaims logical independence and any candidate's hit or miss, and Section 1 supplies an elementary source-backed proof of `MC` even. Only evenness is needed; no stronger mask residue class is assumed.

## 1. Review boundary and exact evidence

I read the final candidate, the complete sealed `Research_Report37.tex`, the relevant cached compiler/source inventories, and the added inert compiler context snapshots. The sealed TeX has SHA256

`57d6598d60389b2fc283f89f47b29ef5905af259ebe0ea69433a8838f9749001`.

I authenticated all five cached upstream source files by byte count, SHA256, and Git blob SHA1 against the sealed manifest. I also checked all four follow-on context snapshots against their pinned SHA256 digests. The new complete77 snapshot has digest `9222a13dc180bd2361877674c4bd957d18f2d9aef827852cf5d320a3d7ac7d7a`; its local contents and exact line ranges were inspected as inert text. Its pinned upstream provenance was supplied by the author; an attempted separate web retrieval returned a cache miss, so I do not claim a second independent network authentication of that file. I did not import or execute any upstream module, evaluate any saved arithmetic schedule, clone a repository, upload an artifact, or write to the sealed tree. All new files are in this `independent/` directory.

The independent checker is `check_audit.py`; its portable frozen receipt is `expected_audit_receipt.json`. It requires Python 3 and SymPy (tested with SymPy 1.14.0). It uses exact symbolic algebra, exact integer arithmetic, and static source-record comparisons. It checks the entire SOS suffix as data, rather than evaluating the upstream schedule. The original five-source authentication and unchanged 43-file sealed-tree snapshot are preserved separately in `historical_audit_receipt.json`. They are historical audit evidence, not checks re-executed by the portable checker. Portable replay authenticates the four packet-relative inert context files and does not depend on a private absolute source path. Normal and `python -O` runs produced identical canonical receipts; the checks use explicit exceptions, so optimization does not disable them. The module is import-safe. Default execution writes only canonical JSON to stdout, `--expect` requires frozen exact-byte equality, and `--output` can create only a new file outside the packet.

The finite fixtures are deliberately labeled abstract contract-compatible subsystem checks. They are not actual compiler exports, not materialized members of the infinite Pell-ratio family, and not full zeros. The proof below, not those fixtures, establishes the infinite theorem.

## 2. Genuine compiler constants and the explicit q

Write `d=d_cell`. Report 37 retains `d=bL`, with `L>=1`, so `b<=d`. For `x>=1`,

    W=2^(2dx+b)<=B^(2x+1),
    q=B^(2x+2),
    q-W>=(B-1)B^(2x+1)>2dx+1.

For the last strict bound, `B^(2x+1)=2^(d(2x+1))>d(2x+1)>2dx+1`, since `d>=4`. This proves the requested integer inequality

    q>=W+u-b+2.

Thus `J=(q-1)/(B-1)` is a positive integer, `q>=B` is even, `3` does not divide `q`, and `q>u-b+2`. With `Z=1`, `C=W+1`, and `alpha_source=q-C-u+b`, the positive raw slack is at least one. Moreover `0<W<q` and `C+u-b<q` hold strictly, before any limiting argument.

The cached source `complete75_half_binomial_compiler.md`, Section 1, equation (3), explicitly gives `MC` even for the modified export. Consequently `(MC+q MFsrc)J=M` is even. No free choice of masks is being substituted. Since `Q` and `C` are odd, while `q`, `W`, and `M` are even, `P0` is odd. Because `L0=q(q-1)Q` is even, its least residue `p0` is odd and nonzero. Every index in that lattice is odd.

The final source-specific parity explanation is correct. The added complete77 snapshot, lines 73–76, gives

    MC0=B-1-sum(Rrad^e for retained positions e other than 1).

Its position construction at lines 83–107 retains position zero exactly once and otherwise uses strictly positive positions. This agrees with the modified compiler note's retained Start selector zero. Since `Rrad` is even, exactly the zero-position summand is odd, while `B-1` is odd. Therefore `MC0` is even. The modified recipe `MC=MC0-2Rrad^e_*` preserves this parity. These are inspections of formula text, not execution of the materializer. The final manuscript appropriately uses only the evenness consequence.

## 3. The outer lattice is exact, without a compatibility assumption

Put `X_r=q^3(1+(q-1)r)` and `D_r=1+q(K0+X_r)`. Direct expansion gives

    Q(D_r C-q^2-W)-M-P0=L0 q^3 C r.

Consequently `p=P0 mod L0` is exactly the required combined packing/transport congruence at every `r`. Division by `Q` is justified, and modulo `q`,

    N=(p+M)/Q=D_r C-q^2-W=1 mod q,

because `C-W=1`. Thus the uniquely recovered marker is exactly `Z=1`, not just some admissible marker.

There is a particularly transparent exact parametrization. With the unrestricted integer

    ell=(p-P0)/L0,

algebra gives

    F=(K0+q^3)C+(q-1)ell,
    z=q^3 C r-ell.

These are the proposed formulas (6a). They prove integrality of both recovered coordinates without any hidden coprimality assumption. Substitution recovers

    -p=(q^2-1-qF)Q+M,
    (K0+X_r)C=F+z(q-1).

The analytic part will select `ell`; it does not need to solve any additional modular compatibility problem. The positivity of the selected `F,z` is checked in Section 6 below.

## 4. Controlled curvature of the exact Binet center

Throughout this analysis `Y=q^3` is fixed before `X` tends to infinity. Let `delta0=(1/2)log(1+1/Y)`, `a0=log(2Y)`, `z=1/X`, and

    v=1/(3log X+4a0).

Set `ea=alpha-log X-a0`, `eb=beta-log X-2a0`, `ek=log K-log Y`, and `d0=2ea+eb`. The explicit epsilon formulas added to the candidate are correct: they are real analytic near `z=0`, their logarithm arguments equal one there, and their constant terms vanish. In particular `(eb-ea)/z` and `d0/z` have removable analytic extensions at zero.

Direct algebra, checked independently symbolically, gives the exact identity

    f(X)=Y/(3z)+(2Ya0/3)v/z+1/3+v G(z,v),

where

    G=[(2Y/3)(eb-ea)/z +(2/3)(a0+eb-ea)
       +2delta0-2ek -(2Ya0/3)v d0/z]/(1+v d0).

The denominator equals one at `(z,v)=(0,0)`. Hence `G` really is analytic in two independent variables on a neighborhood of that point. This proves the proposed asymptotic expansion, including its stated `1/3+O(1/log X)` remainder, rather than merely suggesting it from formal series.

For a full derivative justification, define `R(X)=vG(z,v)`. Near zero, `G` and its partial derivatives through order two are bounded. Along the curve,

    z'=-1/X^2,       z''=2/X^3,
    v'=-3v^2/X,     v''=(3v^2+18v^3)/X^2.

Writing `R` as a function of `z,v`, its derivative factors satisfy

    R_z=O(v), R_v=O(1), R_zz=O(v), R_zv=O(1), R_vv=O(1).

The multivariable chain rule therefore gives

    R''=O(v/X^3+v^2/X^2)=O(1/(X^2(log X)^2)).

Here `1/X=O(v)` for sufficiently large `X`. This explicitly controls the differentiated remainder.

The only curved leading term has the exact second derivative

    d²/dX² [(2Ya0/3) X/(3log X+4a0)]
      =-2Ya0 v^2(1-6v)/X.

It follows that

    f''(X)=-2Ya0/[9X(log X)^2] * (1+O(1/log X)).

The coefficient is strictly positive before the minus sign. This supplies eventual nonvanishing and uniform comparability on every large dyadic interval. There is no illicit differentiation of an uncontrolled big-O term.

Since `X_r=q^3+c0 r`, `c0=q^3(q-1)>0`, the chain rule gives

    g''(r)=c0² f''(X_r)/L0
          =-Kstar/[r(log r)^2]*(1+O(1/log r)),
    Kstar=2Ya0 c0/(9L0)>0.

The replacements `X_r~c0r` and `log X_r=log r+O(1)` are legitimate because every compiler/input/q constant was fixed first. No uniformity over growing `q` is claimed or needed.

## 5. Uniform frequencies and the shrinking interval count

I checked the two cited primary texts. Robert's Theorem 1, Section 3.1, states the second-derivative bound with a constant depending only on the derivative-comparability ratio, and explicitly records uniformity in the phase, interval length, and derivative scale. Mukhopadhyay–Ramaré–Viswanadham's Lemma 6 states the normalized Erdős–Turán bound used in the candidate.

Sources:

- [Robert, Theorem 1, Section 3.1](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
- [Mukhopadhyay, Ramaré and Viswanadham, Lemma 6](https://ramare-olivier.github.io/Maths/Discrepancy-V_5.pdf)

On `N<=r<2N`, the curvature supplies constants `a,b>0`, independent of `N` and frequency, such that

    a/[N(log N)^2] <= |g''(r)| <= b/[N(log N)^2].

For phase `h g(r)`, choose derivative scale `lambda=ah/[N(log N)^2]`. The ratio `b/a` does not depend on `h`. Thus, uniformly for all the frequencies being summed,

    |S_h| << sqrt(hN)/log N + sqrt(N)log N/sqrt(h).

There is no dependence on `h` concealed in this big-O constant. Summing the two terms with weight `1/h` gives

    sum_{h<=Hf}|S_h|/h
       << sqrt(NHf)/log N + sqrt(N)log N,

because `sum h^(-1/2)=O(sqrt Hf)` and `sum h^(-3/2)=O(1)`. With `Hf=floor((log N)^4)`, interval counting error is

    O(N/(log N)^4 + sqrt(N)log N)=o(N/log N).

The interval may depend on `N`: Erdős–Turán controls interval discrepancy uniformly. Its application to `[0,kappa0/log(2N))`, `kappa0=delta0/(8L0)`, is therefore valid. The expected count is `kappa0 N/log(2N)`. For all sufficiently large `N`, the discrepancy is less than half that quantity. Using `log(2N)<=2log N` proves the candidate's lower bound

    delta0 N/(32L0 log N).

For every counted `r`, `r<2N` implies `kappa0/log(2N)<=kappa0/log r`, so it satisfies the desired pointwise shrinking condition. The half-open interval and inclusion of fractional part zero cause no difficulty. Enlarging one finite threshold handles all hypotheses.

The very small fixed `kappa0` can make the threshold enormous. Nothing in this argument supplies a feasible search bound or a uniform complexity result. This limitation is already stated accurately in the candidate.

## 6. Exact Pell acceptance and every strict predicate bound

For a selected `r`, choose `p=p0+L0 floor(g(r))`. Then

    0<=f(X_r)-p<delta0/(8log r).

The non-tail log-ratio is affine in `p` with slope `S(X_r)~(3/2)log r`. Eventually `S<=2log r`; hence rounding down lowers that log-ratio by less than `delta0/4`. Its resulting value lies between `log Y+3delta0/4` and `log Y+delta0`.

Both `p` and `n=(XY+1-p)/2` tend to infinity linearly with `X`. Thus both exact Binet tail arguments tend to zero exponentially in `X log X`. The sum of the absolute logarithmic tail terms is eventually less than `delta0/4`. The full logarithmic ratio is consequently strictly between `log Y` and `log(Y+1)=log Y+2delta0`. This is a proof of the exact integer Pell inequalities, not an approximation test.

The stronger information from the center is

    p=E/3 + Theta(X/log X),
    p/E -> 1/3,  n/E -> 1/3,
    d_def=E+1-2p ~ E/3,

with a positive coefficient in the `Theta` term. The floor error tends to zero on the selected set, and is in any event bounded by `L0`. Therefore one common sufficiently large threshold gives all of the following:

- `p>=13` and odd; `n` is a positive integer because `E` is even
- `u<p`, so the chosen input index `e=u` is admissible
- `p>=ceil(E/3)+1`, since `p-E/3` tends to positive infinity
- `E>=2p+6`, since `E-2p~E/3` tends to infinity
- `E<=3p-3`, since `3p-E` tends to positive infinity
- Consequently `(p+1)/2<=n<=p-1` and `2n-p>=7`
- `p<Xq^4`, since `p/(Xq^4)->1/(3q)<1`
- `4^(2n-p)>X`, since the defect grows linearly in `X`
- `2n+p-1=E`, with the essential `+1` in the definition of `n`
- `s=t=1` satisfy both finite ranges in Report 37

The source's preliminary conditions on `q`, all strict raw loading conditions, and `Z=1` were established in Section 2. Moreover `H>q>W`, so `W=2^u` is exactly the least input residue throughout this family, not merely eventually.

For the outer signs,

    F/X -> Y/(3qQ)=q²/[3(q²-1)]<1.

Thus `F>q` eventually. Also

    ((K0+X)C-F)/X -> C-q²/[3(q²-1)]>0,

so the integral transport quotient `z` is strictly positive. These comparisons use fixed finite compiler numerals, whose constant contributions vanish after division by `X`. This checks every condition in Report 37's predicate other than the deliberately withheld main congruence.

## 7. Positive source completion, including p=1 mod 4

The first block uses exactly the required factor two:

    k_first=2 psi_P(n), tau=chi_P(n), c=psi_A(p).

The exact ratio makes `eta=c-k_first Y` and `zeta=k_first-eta` strictly positive integers. Since `P=1 mod E`, the recurrence gives `psi_P(n)=n mod E`, so

    h=(k_first+p-1)/E

is a positive integer and restored `R=k_first-hE-1=-p` exactly.

The input block with `e=u` needs no main projection. The recurrence modulo `Delta` gives `psi_A(u)=u mod Delta`, because `u` is odd. Pell growth gives positive `delta_input=(psi_A(u)-u)/Delta`, positive `phi=c-psi_A(u)`, and the exact input projection with `W=2^u mod H` gives positive integral `rho`. Report 37's growth argument applies unchanged.

I separately checked the ordinary auxiliary completion for the potentially important `p=1 mod 4` class. Set `m=2cp` in that class and `m=cp` for `p=3 mod 4`. Because `c` is odd, both choices give `ell=p+2m=1 mod 4`. Expansion of `(D+c sqrt Delta)^(m/p)` proves `c²|psi_A(m)`: its first odd term contains `(m/p)c`, and all later odd terms contain `c³`.

For `T=Delta psi_A(m)`, `f_aux=chi_A(m)`, this makes `i=T/c²` a positive integer and gives the ordinary strong norm. For odd `ell=2h+1`, the polynomial `chi_T(ell)/T=Q_h(T²)` satisfies

    Q_h(0)=(-1)^h ell,
    Q_h(1-A²)=(-1)^h psi_A(ell).

Here `h` is even, which is exactly the sign issue addressed by the two-case choice of `m`. Modulo `c`, the first identity gives `U=p mod c`; modulo `f_aux`, the second identity and the Pell addition formulas give `U=-c mod f_aux`. Hence `j=(U-p)/c` and `o=(U+c)/f_aux` are integers, and their positivity follows from `U>=4T²-3>p`. The norm at base `T` supplies the remaining mixed-sign auxiliary equation with positive `y_aux`.

No part of that construction uses `2^p=X mod H`. The `p=1 mod 4` case is covered by the essential factor two in `m`; replacing it with the older `p=3 mod 4`-only construction would be an error, but the candidate does not do that.

## 8. The literal one-residual claim

Let `D=chi_A(p)` and use the positive integer

    ga=floor((D-ac-X)/H).

Report 37's exact relation `D-ac=2psi_A(p)-psi_A(p-1)>psi_A(p)>H+X` ensures that this floor is at least one, without needing divisibility by `H`. Let

    r_main=D-ac-X-ga H,  0<=r_main<H.

The exact recurrence gives `D-ac=2^p mod H`; hence `r_main=(2^p-X) mod H`. Every supplied raw coordinate is positive, and the preceding constructions make all raw comparisons zero except

    D-(X+ac+ga H)=r_main.

Static inspection of the cached raw source shows that `ga` affects only raw comparison 9; the source finalizer contains every one of its 18 squared comparisons exactly once. The raw polynomial value is therefore precisely `r_main²`.

In positive21, the removed main-root coordinate is the triangular expression

    D'=X+ac+ga H=D-r_main>0.

The other eliminated coordinates reconstruct their same values. Static dependency inspection shows that `ga` affects only retained comparison 4, corresponding to raw main norm comparison 10. That norm's residual is

    (D-r_main)²-Delta c²-1=-r_main(2D-r_main).

Its complete ten-term SOS therefore has value `[r_main(2D-r_main)]²`. Since `D>H>r_main`, it vanishes exactly when `r_main=0`. This is the claimed literal one-residual realization, including the difference between the raw and triangular interfaces.

## 9. The separate sharpened estimate

For any putative full zero in the unwrapped sector, `q>W=2^b B^(2x)>=2B²>K0`. Therefore

    K0(q²-1)<q³<=X,
    q(q²-1)(K0+X)<Xq³.

Positive transport gives `F<(K0+X)C`. Positive packing, `Z<q<q²`, and `M>0` then give

    p<Q[Z+q(K0+X)C-q²]-M<qQ(K0+X)C<CXq³.

Together with `ts Xq³=tE<=3p-3`, this yields `ts<3C`. The stated strengthening is correct; it supplies no global sign conclusion.

## 10. Receipt summary and conclusion

The exact checker records:

- Historical evidence of five authenticated cached source identities and 43 unchanged sealed files
- Four packet-relative context digest checks in portable replay
- Exact symbolic analytic-remainder and curvature identities
- Exact symbolic affine lattice, packing, transport, and shifted-root residual identities
- Both complete supplied-coordinate inventories and SOS suffixes, checked statically
- 432 abstract bound/lattice fixtures
- 20 `p>=13`, `p=1 mod 4` modular auxiliary fixtures
- 25 exact odd-quotient polynomial identities
- Identical normal and optimized run receipts

These checks corroborate the algebra. They do not replace the analytic proof or certify a finite genuine-compiler example.

**Bottom line:** the proposed infinite family rigorously satisfies the reduced Report 37 predicate on every fixed genuine compiler/input slice, with the stated dyadic lower count. Its unresolved residue remains exactly the missing main exponential congruence. The full negative-zero question is still open.

## Portable replay

From the packet root, with Python 3 and SymPy installed:

    python independent/check_audit.py --expect independent/expected_audit_receipt.json
    python -O independent/check_audit.py --expect independent/expected_audit_receipt.json

Both commands emit the canonical frozen receipt on stdout. For a file, add `--output` with a fresh path outside the packet. There is no in-place expected-receipt update mode. The frozen comparison includes manuscript, author-checker, independent-checker, review, context, and historical-receipt fingerprints.
