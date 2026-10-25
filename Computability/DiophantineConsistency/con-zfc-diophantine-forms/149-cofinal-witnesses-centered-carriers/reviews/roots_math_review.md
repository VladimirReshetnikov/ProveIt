# Independent review: centered two-root and three-root charts

**Verdict: PASS for the new arithmetic reductions, literal artifacts, exact degrees,
and operation counts.** No mathematical defect was found in `roots/PROOF.md`.
The inherited source/native/refutation calibration remains an explicitly imported
ordinary mathematical theorem, not a new finite-test or proof-assistant result.

Reviewed on 2026-10-25. The audit read the producer's proof, builder, checker,
circuit implementation, coefficient wrapper and finite recipe before execution.
It independently read the retained fifteen-variable parent and calibration
boundary. This review does not alter the polynomial artifacts or publish anything.

## 1. Verified results and comparison

| Chart | Unrestricted integer inputs | Exact degree | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|---:|---:|
| Centered two-root | 14 | 88 | 64 | 23 | 23 | 110 |
| Centered three-root | 13 | 156 | 70 | 23 | 24 | 117 |

The fourteen-variable chart saves five operations against the retained
14/88/115 chart. It strictly dominates 14/94/110, but trades degree against the
retained 14/86/112 chart. The thirteen-variable chart saves eight operations
against 13/156/125 at unchanged degree. These are arithmetic-DAG lengths,
not bit-complexity claims or global lower bounds.

All 186 retained files, excluding generated Python caches, are byte-identical
to `round18/roots/deliverable/`. Both DAGs and both specifications, together with
`METRICS.json`, are reproduced byte-for-byte by running the inspected builder
in a separate temporary copy. The independent checker imports no producer
builder, circuit, checker, or audit module.

## 2. Unconditional arithmetic prerequisites

Use the abbreviations of `roots/PROOF.md`. With the actual fixed
`beta=2^1064921-1`, `q=beta(6j+1)+1` is even and nonzero. `H=4a+3` is odd and
nonzero, hence `U=2q^3 H` never vanishes on an integer assignment. Since
`W=12w+4`, we have `|W|>=4`, `|X|>=8`, and `a=(X+1)Y` is either zero or has
absolute value at least seven. Consequently

    Delta=(a+2)^2-1 >= 3.

Set `D=XY^2`. Then `D` is even, `L=Dk`, and

    Dt=1+D(D+1)k^2 >= 1,

with `Dt` odd. In the thirteen-variable chart
`Fs=1+Delta I^2 >= 1`; no assertion that `Fs` is odd is needed.
The residue exclusion for the strong unit is sound:
`B=f^2-Delta I^2-1` is never two modulo four, so `B!=-2`.

The exact parent identity, independently verified, is

    (Z+Uk)^2+4U(LZ-U) = (Z+U(2L+k))^2-4U^2 Dt.

This includes both terms in the corrected degree-22 parent leading form;
the known inherited omission is not reused as a complete leading-form claim.

## 3. Fourteen-variable zero maps, including both delicate branches

Write `b=2L+k`, `rho=Z/U`, and `Aroot=4Dt`. The centered norm equation is

    (rho^2-Aroot-G)^2-4Aroot G=0.                         (A)

The finalizer `(N2+1) S Ea-1` is exact: all three factors must be integer
units; `N2` is a square modulo four and `S=B+1` cannot be minus one. Thus
every finalizer zero has exactly `N2=0`, `B=0`, and `Ea=1`.

If `G<0`, the left side of (A) is a square plus a strictly positive number.
Thus `G>=0`, and

    budget=G+1+p2^2+p3(p3+1)>0.

The integer product `p3(p3+1)` is nonnegative. The budget is nonpositive
when either `Y=0` or `k=0`, hence both are nonzero at a new zero. Therefore
`|D|>=8`, and the stated strict carrier bound is valid:

    Aroot >= 4+2X^2 Y^4 k^2
          >= 4+32q^2 Y^4 k^2
           > q^2 Y^2 k^2 >= budget > G.

In particular, `rho=0` would imply `Aroot=G` in (A), a contradiction.
This proves nonzero carrier **before** the following division:

    p=(rho^2+G-Aroot)/(2rho),  u=rho-p.

The independently checked extraction identity gives `p^2=G`; substitution
gives `u^2=Aroot`. A rational number with integral square is integral by
reduction to a coprime numerator and denominator. Hence `p,u` are integers,
`u` is even, and `tau=u/2` satisfies `tau^2=Dt`. When `G=0`, this argument
retains the valid branch `p=0` and `rho^2=Aroot>0`; it does not divide by
`G` or discard that branch.

Restore the parent by

    p1_old=p,  n_old=n-b-p,

leaving every other parent input unchanged. The centered old carrier is
`Z_old/U+b=rho-p=2tau`, so the parent carrier vanishes. The strong and
auxiliary rows are unchanged, and `p^2=G` restores its exact guard.

Conversely, from every parent zero the rational number `Z_old/U+b` has
square `4Dt`, hence is an even integer `2tau`. Keep the shared coordinates,
delete `p1`, and set

    n_new=n_old+b+p1_old.

Then `rho=2tau+p1_old`, `G=p1_old^2`, and (A) vanishes identically. This
is a map on **every** parent zero, with no canonical-witness assumption.

## 4. Thirteen-variable signed extraction and all cancellation classes

The independently multiplied eight signed factors give exactly

    N3/U^8 = product_(e1,e2,e3 in {+1,-1})
      (rho-e1 sqrt(G)-2e2 sqrt(Dt)-4e3 sqrt(Fs)).           (B)

`N3` is a square modulo four, so the unit-product finalizer gives precisely
`N3=0` and `Ea=1`. Here `G=1 mod 4`, so `G=0` is impossible. If `G<0`,
each factor in (B) has nonzero imaginary part: `sqrt(G)` is the only
imaginary radical, while `rho`, `sqrt(Dt)`, and `sqrt(Fs)` are real.
Consequently a zero forces `G>0`.

Write each positive radicand as `ui^2 di`, with `di` squarefree. Distinct
squarefree radicals, including `sqrt(1)`, are linearly independent over the
rationals; their sign characters in the field generated by all involved
prime square roots supply the usual projection proof. In a vanishing factor,
group terms by squarefree class. Every irrational class would need coefficient
zero. This is impossible:

* A class containing the `G` term has an odd coefficient plus even terms.
* A class without `G` but containing `Dt` has coefficient twice an odd
  integer plus a multiple of four.
* A class containing only `Fs` has one nonzero coefficient.

Oddness of `G` and `Dt` ensures their square parts are odd. The argument
does not require distinct classes or odd `Fs`; an even squarefree class
can contain only `Fs` and is excluded by the last case. Thus all classes
are rational, and the signs in a vanishing factor give integers

    g^2=G,  tau^2=Dt,  f^2=Fs,  rho=g+2tau+4f.

`g` and `rho` are odd, so carrier zero is impossible without any division
by `rho`. Restore the parent using

    f_old=f,  p3_old=(g-1)/2,  n_old=n-b-g-4f.

The parent carrier equals zero by `Z_old/U+b=2tau`; its strong equation
is `f^2=Fs`; its auxiliary interface agrees because every eliminated
`f^2` was replaced by `Fs`; and
`p3_old(p3_old+1)=(G-1)/4` restores the guard exactly.

Conversely, any parent zero supplies `g=2p3_old+1` and an integral `tau`
as above. Deleting `f,p3` and putting

    n_new=n_old+b+g+4f_old

forces a signed factor in (B) to vanish. No new Pell existence result is
used. The root-dependent restorations need not be bijections; the separately
claimed shear below really is a bijection.

## 5. Exact old-polynomial shear

Only the shared register `Z` depends on `n`, and its coefficient of `n`
is exactly `U`. Independent cut checks validated the shared front in both
new and frozen old DAGs. Then the actual frozen output DAGs, not merely
their printed norm descriptions, were compared symbolically under

    Z_old=Z_new-U(2L+k).

The complete output difference is identically zero for both charts.
Therefore `P_new(n)=P_old(n-b)` with all remaining inputs fixed. Since
`b` is an integer polynomial independent of `n`, the inverse is `n->n+b`.
These are polynomial automorphisms of the full integer coordinate spaces
and bijections of the corresponding complete integer zero sets.

## 6. Full leading forms and exact numeral-specialized degree

Put

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=q0^4 z-12q0^3 w C, a0=X0Y0,
    U0=8q0^3 X0Y0, L0=X0Y0^2 R0.

Independent propagation through every actual gate, with coefficient ports
of degree zero, gives the complete forms

    (N2)_60=U0^4 R0^4(q0^8+4X0^2Y0^4)^2,
    (P14)_88=-8a0^4 r^2 c^4 f^4 R0 y (N2)_60;

    (N3)_120=256U0^8 R0^8(q0^8+X0^2Y0^4)^4,
    (P13)_156=32a0^6 r^4 c^8 R0 y (N3)_120.

The whole output top forms have respectively 18 and 50 expanded terms.
Their independently checked coefficient witnesses are

    [j^56 w^8 v^8 z^5 r^2 c^4 f^4 y] P14
      = -2^87 3^64 beta^56,
    [j^106 w^14 v^14 z^9 r^4 c^8 y] P13
      = 2^171 3^120 beta^106.

The exponent sums are 88 and 156. The authenticated fixed beta is nonzero,
so these are exact degrees at the actual coefficient tuple, not merely
generic symbolic-port upper bounds. Every input and all six ports are live.

## 7. The all-polynomial n-only obstruction is valid, but scoped

Let `n->n+H` with `H` independent of `n` and with fixed real coefficients.
For degree at most nine, let `H9` be its degree-nine homogeneous part,
possibly zero. Since the original `Z` has degree seven, the only possible
degree-fifteen new carrier part is `U0 H9`.

For the two-root norm its degree-60 form is

    U0^4[(H9^2+R0^2q0^8-4L0^2)^2+(4R0q0^4L0)^2].

For the three-root inner polynomial its degree-60 form is

    U0^4[(H9^2+4R0^2q0^8-4L0^2)^2+(8R0q0^4L0)^2].

Both identities were independently checked. Each second summand is a
nonzero square. A sum of real polynomial squares cannot vanish identically,
so these top forms survive for **every** such `H9`, including choices
involving the other retained variables. In the three-root case the outer
subtracted product has degree at most 114 and cannot cancel the square's
degree 120. Unchanged finalizer degrees are 28 and 36. Thus the resulting
output degrees stay exactly 88 and 156.

If `m=deg(H)>9`, the carrier has degree `m+6>15`, whose highest powers
strictly dominate the fixed radicands. The output degrees become
`4m+52` and `8m+84`, respectively, and strictly increase. Therefore no
polynomial shear of `n` alone lowers these degrees. Allowing real
coefficients strengthens this algebraic degree statement; integer
coefficients are required for the asserted integer-coordinate automorphisms.
Nothing here bounds transformations of other coordinates, arbitrary
polynomial automorphisms, alternative eliminations, or all equivalent
polynomials. **It is not a global-minimality theorem.**

## 8. Complete coefficients and exact calibration boundary

All six full fixed integers are present as minimal unsigned little-endian
payloads compressed by gzip in `inherited/baseline/coefficients/`. The
binding uses the already shifted convention `MF=MF_native+beta`.

| Port | Bits | Raw bytes | Raw SHA-256 |
|---|---:|---:|---|
| beta | 1,064,921 | 133,116 | `6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea` |
| K0 | 1,065,043 | 133,131 | `18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af` |
| MC | 1,064,921 | 133,116 | `3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777` |
| MF | 1,064,922 | 133,116 | `78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722` |
| cone_A | 1,114 | 140 | `66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615` |
| cone_B | 666,105 | 83,264 | `42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401` |

All **615,883 raw bytes** were authenticated independently. The three
literal values `beta=2^1064921-1`, `cone_A=2^1113`, and `cone_B=2^666104`
were also checked directly. The inspected retained `construct()` recipe
reconstructed every byte of all six integers in normal and optimized
Python, with identical receipts. This is a finite coefficient reconstruction,
not simulation of an unbounded blank computation or a consistency search.

The precise new result is equivalence to the zero set of the retained
fifteen-variable parent, by the universal maps above. The subsequent chain
uses `FREE_SCALE15_PROOF.md` and the pinned signed-Pell/source34/native
compiler and machine/refutation ordinary proofs. In particular,
`source_closure/provenance/rootfusion/CALIBRATION_STATUS.md` identifies
the ordinary composition to syntactic `Con(ZFC)` and distinguishes it
from the separately open encoded-object-language target recorded in
`FORMALIZATION_BOUNDARY.md`.

No new Lean compilation, kernel certificate, sealed object-language ZFC
derivation, or independent reproof of the full transitive calibration was
performed or is claimed. If that imported ordinary calibration is not
accepted, the audited unconditional deliverable here is the exact
source-zero equivalence; its final `Con(ZFC)` interpretation is conditional
on the named calibration. No test proves consistency or inconsistency.

## 9. Reproducible audit evidence

* `roots_independent_audit.py`: separate hand-specified arithmetic cuts,
  frozen prior-front and whole-output shear checks, topology/liveness/counts,
  full norm and output top forms, coefficient witnesses, all signed factors,
  rational extraction/restoration, and both general degree-nine SOS identities.
* `roots_independent_normal.json` and `roots_independent_optimized.json`:
  PASS; identical evidence apart from the optimization-mode flag.
* `roots_check_normal.txt` and `roots_check_optimized.txt`: inspected producer
  checker PASS, including rejection of all 110 and all 117 one-gate mutations.
* `roots_independent_rebuild.json`: byte-identical copied-tree rebuild.
* `roots_round18_comparison.json`: 186 retained files, no deviations.
* `roots_coefficients_normal.txt` and `roots_coefficients_optimized.txt`:
  full finite reconstruction PASS, byte-identical receipts.

The infinite sign/square-class and arbitrary-shear claims are justified by
the ordinary proofs in Sections 3, 4 and 7, not inferred from finite samples.
