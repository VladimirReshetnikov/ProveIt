# Independent mathematical review of the eleven-positive construction

Reviewed: `work/positive_reduction/ELEVEN_POSITIVE_PROOF.md` and
`build_eleven.py`, in the same research session. The source snapshot for
inherited facts is ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

Outcome: no mathematical blocker found in the new local reduction.
This is a separate mathematical review, not a Lean/Rocq certificate.

## Decisive points checked

1. The sharp root bound uses no deleted index equation. Expanding
   `(a+2)^2(1+1/Y)/E` gives exactly the stated identity. With X>=16 and
   Y>3q^4, its remainder is below one and the Cstar margin is sufficient.
   The linear-T term is bounded by 2TI using `(a+3)(1+1/Y)/E<2`.
   The argument covers complex auxiliary roots by absolute values.

2. The centered carrier excludes the negative main-root branch before
   recovering the index congruence. Both b0 and sqrt(G) exceed sqrt(A),
   while `t+(k-R-1)/E>0`. Thus a negative branch would exceed the universal
   inner-root bound. If G is nonsquare, actual quadratic conjugation
   produces this forbidden branch, without assuming independent radical
   fields. This correctly recovers the positive integral main root.

3. After this recovery, the normal-closure automorphism argument for the
   first root is valid: an automorphism negating an irrational tau fixes
   rational x, and both auxiliary conjugates obey the strict root bound.
   Rationality of f and Pell saturation then recover integer auxiliary
   roots. No unproved denominator cancellation occurs.

4. The carrier initially gives only `E | H(k-R-1)`. The proof explicitly
   retains gcd(E,H), rather than incorrectly cancelling H. This is the
   crucial weaker divisibility and the new proof uses it correctly.

5. The main Pell rank p can be recovered before either h or gamma.
   `c=psi_A(p)` and `c^2 | psi_A(m)` imply `p | m`, then `pc | m` from
   the quotient recurrence modulo c and coprimality of the Pell abscissa
   with c. This is the direct normalized strong-rank argument in the
   pinned `complete84_signed_quotient_absorption.md`, Section2; its old
   large-c hypothesis is explicitly unnecessary for this direct route.
   Here c>6R and p>=2 imply both R,p<c/2, while m>2p. The signed auxiliary
   residues and ordinary index step-down therefore yield p=R, with no
   use of the deleted index congruence. Signs of f and V remain allowed.

6. The short-range congruence closes the reduction. Since
   `gcd(XY,H)` divides `X gcd(Y,H)` and `gcd(Y,H)=gcd(Y,3)`, the remaining
   modulus `mu=E/gcd(E,H)` is at least Y/3>R. First-Pell monotonicity gives
   1<=n<R. Hence `2n=R+1 mod mu` and `|2n-R-1|<R` imply exact equality.
   Reducing the first Pell recurrence modulo the full E now restores
   E|(k-R-1), and its quotient h is positive because n>=25. Only after
   this restoration is gamma recovered modulo H, with its positivity
   following from c>X. The logical order is noncircular.

7. Completeness of the shifted s coordinate is justified by an actual
   inherited theorem: `ORDINARY_BLANK_PROOF.md`, around line269, proves
   `Y>X^r/3>2^R` in the canonical/main-rank branch. With R>3q and q>=16
   this gives s_old>3q. The new carrier t is positive because M tau>h.
   The shifted transport coordinate is also justified by w>q>F.

8. The scalar circuit is the eight-factor norm with H replaced by S.
   The reversed sign convention for vr is handled consistently by
   N=right-left. Its mod4 square residue gives the two-factor product
   finalizer directly, forcing Nt=1 and N=0. Thus the deleted index
   factor introduces no unresolved unit sign.

9. The exact degree transfer multiplies every conjugate factor by E^2,
   hence the full norm by E^16. The rational carrier correction has
   degree -2 instead of1; it cannot change the predecessor's highest
   homogeneous term. The s substitution has invertible linear highest
   part. The claimed norm degree1152 and product degree1154 follow
   from the pinned predecessor degree1056 and its nonzero leading form.

## Optional degree1140 translation

The separate `OPTIONAL_TRANSLATION_PROOF.md` was also reviewed. No
mathematical blocker was found in the positive-domain substitution
`t_old=t+sigma`, where `sigma=M(ell+2c-X)-b`.

* The exact expansion of `Cstar*ell-Delta*c` includes the term
  `-4E*eta`. Absorbing it into `-E*Y*eta` is valid because Y>=4.
  The resulting eta and zeta coefficients are each at least X/2 for
  X>=16 and q>=16. With c<k(Y+1), this proves the claimed lower bound
  `(k/3)X^2Y^2` independently of any bound k>E.
* `Cstar<3XY/2` follows directly by dividing by XY. Thus
  `Cstar(ell+2c-X)-Delta*c>X^2Y>1`. Expanding sigma gives
  `2TI(ell+2c-X)+R i^2 c^3[the bracket]-c-R`, which is positive already
  from c>=2 and R>=1. Every prospective new root therefore gives an
  admissible positive old carrier.
* For a canonical witness, the inverse shift is exactly
  `gamma+M[(tau-ell)-(A0*c-g)]+y+b-h`. Rationalizing the two positive
  radical differences gives `tau-ell>k/3` and
  `A0*c-g<c/A0<2k/(X+1)<k/3`. The inherited canonical roots gamma,y
  are positive, and b>c>k>h. The inverse shift is therefore positive.
* In the sixteen-factor Laurent expansion, exactly two old factors
  with leading term -C0 lose their degree35 term; their new degree28
  leader is `-M0*k0/2`. The other two degree35 factors acquire leader
  2C0; the degree36 and degree38 factors are unchanged at highest order.
  Hence the degree decreases by14. The leading-form ratio is
  `M0^2*k0^2/C0^2=1/(s00^4*q0^10)`, giving the displayed norm leader
  `2^46 i^48 k0^96 w^90 s00^188 q0^700(q0-F)^16` and exact degree1138.
  The product has degree1140 after multiplying by the degree2 transport
  factor. The additional rational index shift has degree-2 and cannot
  change any of these branch leaders.

The translated companion consequently improves degree at the cost of six
additional arithmetic gates; it preserves eleven positive variables and
the same four coefficient ports and inherited compiler dependencies.

## Scope

The review checks the new mathematical reduction and its interface order.
The inherited unbounded native compiler and K215 syntactic-refutation
calibration remain explicit dependencies; no finite numerical check is
being offered as a substitute for them. The result improves the direct
moderate-degree family from twelve to eleven positive supplied unknowns;
it does not beat nine-variable Jones constructions on variable count or
the historical operation minimum on evaluation cost.
