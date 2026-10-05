# A cross-block multiplication boundary and an exact outer-mask tie

No operation saving was found. This note proves an unbounded, explicitly restricted eight-multiplication lower bound spanning the scale, first-norm and index producers, and gives a six-row outer-mask refactor whose complete source still costs **84 = 47M + 37A**. Neither result is a lower bound for arbitrary circuits computing the complete polynomial or its positive zero set.

## 1. Actual source and novelty boundary

The parent is `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json`, SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Its full saved array has84 live rows,25 live supplied ports,18 positive witnesses and six fixed compiler numerals. Its companion, SHA256 `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`, proves the inherited positive-zero equivalence and exact degree187. Those native and universality theorems are inherited, not reproved here.

The bounded local-producer and shared-fork searches already exclude their stated small replacement grammars. The polynomial-multiplier first-norm bound starts with `E=XY` and `Z=kY` already paid. The present multiplication bound instead charges those producers together with their actual scale and index consumers, and allows arbitrarily many multiplication gates and arbitrary scheduling. It does not broaden the earlier lower bounds to additional nonmonomial donors.

## 2. Eight products are necessary at this shared monomial boundary

Use five independent paid polynomial coordinates `q,k,w,s,h`, with `k=R10b` in the actual source. Fixed scalar coefficients may be free, which only strengthens the lower bound. Allowed gates are multiplication only; no additions, subtractions, division, outside computed registers or change of boundary outputs is allowed. The required values are

    X = wq,
    Y = sq³,
    E = XY = wsq⁴,
    Zk = kY = ksq³,
    U = E Zk = kws²q⁷,
    hE = hwsq⁴.

One may additionally require `q²`; the lower bound below does not need that extra output. We work in characteristic zero, with nonzero monomials distinguished up to nonzero scalar multiples.

**Proposition.** Every such multiplication-only circuit producing these six values has at least eight multiplication gates.

**Proof.** Every nonzero wire is a scalar times a monomial with nonnegative exponents. Every ancestor of the output `Y=sq³` is therefore independent of `w,k,h`: introducing any of those variables cannot subsequently be undone by multiplication. Ignore scalar-only gates. A circuit producing `sq³` from `q,s` needs at least three products. Indeed, with at most two products the first nonconstant product has total degree at most2. To obtain degree4 at the second gate, both operands must be the first degree2 product; the result is its square, whose exponents are even. The exponents `(3,1)` of `sq³` are not both even. A later multiplication by a free scalar does not change this obstruction.

The other five required target monomials are distinct from each other, are not supplied leaves, and each contains at least one of `w,k,h`. Each therefore requires a distinct product gate outside the ancestor cone of `Y`. The total is at least `3+5=8`. This proof permits arbitrary fanout, squaring and topological reorderings. ∎

The actual source attains eight products, at its one-based row numbers:

| Row | Register | Paid product |
|---:|---|---|
|4|`Lbig`|`q*q`|
|5|`n2`|`Lbig*q`|
|6|`wn2`|`w*q`|
|7|`sn2`|`s*n2`|
|8|`UM`|`wn2*sn2`|
|10|`ksn2`|`R10b*sn2`|
|11|`first_root_base`|`UM*ksn2`|
|50|`hpm1`|`h*UM`|

Here `Lbig=q²` is also used by the original outer block. The six-target proof remains applicable if that outer use is removed: it does not silently rely on `q²` remaining an externally required result. The other source rows, including the paid addition forming `k`, are outside this count and remain charged in the complete84 ledger.

This excludes a one-product improvement by monomial reassociation of this entire cone. It does **not** exclude a circuit using addition and cancellation, a donor outside the stated cut, a different first/input norm identity, or a positive-coordinate chart that changes the retained outputs.

## 3. A six-row mask factorization ties on the same supplied interface

Write `m=Bm1`, `J=Jrep`, `g=gap`. The actual earlier rows give `q=mJ+1` and `Lbig=q²`. Parent rows54–59 are

    Lm1        = Lbig - 1
    rproduct   = gap * Lm1
    qMF        = q * MF
    mask_factor= MC + qMF
    mask       = mask_factor * Jrep
    r_lhs      = rproduct + mask.

These six rows cost3M+3A. On the same six fixed-numeral interface, replace them by

    cross_mask_t   = Bm1 * gap
    cross_mask_u   = cross_mask_t + MF
    cross_mask_v   = q * cross_mask_u
    cross_mask_w   = cross_mask_t + MC
    cross_mask_sum = cross_mask_v + cross_mask_w
    r_lhs          = Jrep * cross_mask_sum.

These also cost3M+3A. Exact expansion gives

    J[q(mg+MF)+mg+MC]
      = J[m(q+1)g+q MF+MC]
      = (q²−1)g + J(MC+q MF),

because `mJ=q−1`. This is an identity over every commutative ring after the actual paid definition of `q` is substituted. `MF` is the inherited shifted source port; no replacement by the unshifted native mask is made. There are no extra fixed constants, divisions, positivity assumptions or unit-equation substitutions.

The alternate notation `J[(q+1)(mg+MF)+(MC−MF)]` can obscure a charge: computing `MC−MF` at the unchanged symbolic interface would cost an extra addition. The six-row schedule above avoids that charge altogether, but still supplies no saving.

The fresh check emits the entire replacement array. Exactly78 rows outside this cut remain literally unchanged; the79 common computed values consist of those78 plus the algebraically equal `r_lhs`. All25 supplied values are also identical. Every row and supplied port remains live, so there is no hidden deletion after the local count. The complete output is the identical polynomial, with84 operations,18 witnesses and inherited exact degree187. In particular its full positive zero set is identical on the parent's valid fixed-program domain; no new domain argument is needed.

## 4. Evidence, read scope and next boundary

Fresh `/tmp/complete84_cross_block_next_checks.py` reads the pinned parent JSON as data. It verifies the literal old rows and actual `q` producers, reconstructs all84 replacement rows, checks topology/liveness/ledger, proves the local identity by exact integer sparse-polynomial expansion, and lifts that identity through all common source values by row induction. It separately derives all seven monomial exponent vectors and checks the simpler seven-output obstruction: no product of paid leaves or other target monomials can first produce `Y`. The stronger six-output theorem in Section2 is the mathematical argument above, not an inference from finite samples.

The writer and fresh normal/`-O` exact receipt checks from `/` passed before freezing. No predecessor helper, compiler, supplied program or archived program was executed or imported. The source Python parent was only hashed. No numerical evaluation was used to certify an identity.

Frozen fresh evidence:

- Checker `/tmp/complete84_cross_block_next_checks.py`: SHA256 `5197d2da12b8d2e8b17d0fc5953898d242f769a5417797deac192f01708f4b64`.
- Receipt/full tied array `/tmp/complete84_cross_block_next_checks.json`: SHA256 `d9794f7ebb9678635846bf0444edd7635857ce15f7275bbb5dbc672aea697616`.

Prior scope documents read inertly, in the same repository directory:

| Document | SHA256 |
|---|---|
|`complete84_local_producer_scout.md`|`7cfa58529ec02a6cf3df475e3d0feda6b4e5f4ad6b6c622e810907371b0aecad`|
|`complete84_shared_fork_scout.md`|`d2ba717ab229d830a4b73002edddd401c3f2046f46cdb050c6fcdceccaae091c`|
|`first_norm_polynomial_scaling_bound.md`|`ade14fbd609acc0b9aff5b559fbe31e1527057afb2265b94a24cb9dffb978ca3`|
|`complete84_joint_root_cut.md`|`79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c`|
|`complete84_actual_modulus_scout.md`|`068c5efb6d2fc6d011334d4e0cf7384e5d6d048ec64cee1c2161bb126cb173a1`|

The new obstruction concerns the producer cone rather than the exhausted auxiliary ten-gate interface. A further saving must leave this multiplication-only boundary, for example through joint nonmonomial norm arithmetic or a proved positive chart. This note proposes no universal83 source and no unrestricted84 optimality claim.
