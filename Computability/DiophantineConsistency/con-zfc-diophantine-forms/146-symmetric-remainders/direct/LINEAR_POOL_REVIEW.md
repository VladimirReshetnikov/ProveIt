# A nine-term linear orientation pool for the cofinal signed-anchor compiler

This is an ordinary unbounded derivation, independently checked against the
local Cofinal Anchors and Local Certificates packages. It is an internal
research note for the parent agent. All indices and coefficients below are
finite fixed data in the delivered compiler. No claim of a new foundational
calibration is made.

## 1. The exact replacement

The cofinal compiler has fourteen distinct principal Pell pairs after its
`K=x` identification. Their proposed indices are

`t, F^2+t, a, b, c, d, S, y+1, Sp, u, x, vq, C0, h`.

Let `I` be the nine CRT-representative pairs, with indices

`a,b,c,d,S,Sp,u,vq,C0`.

Replace its pooled equation by

    sum_all (Y_i-k_i)^2 + sum_(i in I) (1-X_i) = (A-1) Q.

Here `Q` is the same private, unrestricted integer quotient. No additional
coordinate or inequality is introduced. The previous pool used
`sum_all [(X_i-1)^2+(Y_i-k_i)^2]`.

This is more economical than changing all fourteen squares into linear
terms: five abscissa orientations follow from the already-required power
requests and do not need their own terms at all.

## 2. The finite-alphabet lemma at either sign of A

The unchanged square frame and anchor provide `W>=258`, `|A|>W^W`,
`|A-1|>4W^3`, absolute actual Pell indices `0<=j_i<W`, and
`|k_i|<W`. Write the small recurrence residues modulo `A-1` as

    X_i = s_i mod(A-1),    Y_i = r_i mod(A-1),

where `s_i` is either +1 or -1 and `r_i` is either +j_i or -j_i.
This also holds for negative A, by the parity identities for the Pell
polynomials. The new pool gives divisibility of

    E = sum_all (r_i-k_i)^2 + sum_(i in I) (1-s_i).

Each orientation summand belongs to `{0,2}`. Thus

    0 <= E < 4*14*W^2 + 18 < 4W^3 < |A-1|.

Consequently E=0, all ordinates are the canonical signed-index values
`Y_i=Y_(k_i)(A)`, and the nine selected abscissas equal
`X_(k_i)(A)`. The actual large left side of the pool need be neither
small nor nonnegative; only its small residue representative E is used.

## 3. Complete sign table for a power request

Let `2<=n<W`, `|k|<W`, `|m|<W`, and `T=2An-n^2-1`.
With a canonical ordinate `Y_k(A)`, consider

    X+(n-A)Y_k(A) = m + T z.

For a positive index j, put

    H_j=X_j(A)+(n-A)Y_j(A),
    J_j=X_j(A)-(n-A)Y_j(A).

Pell identities give `H_j=n^j mod T` and `H_j J_j=1 mod T`.
The frame gives `|T|>W^W+W`. Every relevant small congruence therefore
becomes an exact equality: `|m*n^j +/- 1|<W^W+1<|T|` and
`|m +/- n^j|<|T|`.

* If `k=j>0`, the abscissa `+X_j(A)` gives `m=n^j`; the opposite
  abscissa would give `m*n^j=-1`, which is impossible.
* If `k=-j<0`, the abscissa `+X_j(A)` would give `m*n^j=1`, which is
  impossible; the opposite abscissa gives `m=-n^j`.
* If `k=0`, the two abscissas are `+1` and `-1`, and respectively give
  `m=1` and `m=-1`.

Two useful consequences are: a known positive index forces the correct
abscissa and power output; a known output `m>=2` forces a positive index
and the correct abscissa. A selected, already-canonical abscissa forces
`k>=0` and `m=n^k`.

These facts are valid for signed A. Here a 'correct abscissa' means the
Pell polynomial at A; it need not be a positive integer when A is negative.

## 4. A noncircular recovery order with only nine orientation terms

1. Initially the retained scalar guards give `B>=1`, `q>=2`, and the
   cofinal horizon gives `t>=16`. Apply the positive-index power argument
   to the genuine `q^t` request. It forces the t abscissa to be canonical.
   The same pair then interprets `V0=(F^2+1)^t`, including its base-one
   possibility.

2. The ceiling identity `FB=V0+s`, with `s>=0`, gives `F>=1` and then
   `B>=2`, `q>=3`. The retained beta equation gives
   `y=V0(V0-1)>F+2`.

3. The nine selected CRT pairs are canonical. Each has a request at the
   positive base `q+1>=4`. The power lemma therefore proves that all nine
   actual representatives are nonnegative and their numerator requests are
   exact. In particular `H0=1+sum(actual representatives)>=1`.

4. The x pair is shared by the three requests with bases `B`, `B H0`,
   and `q`. In the `B H0` request its output is the actual already-positive
   q. Since `B H0>=2` and `q>=3`, the positive-output part of the sign table
   forces `x>0` and the canonical x abscissa. Thus all three x requests
   become exact. This step does not presume x nonnegative or use the
   endpoint inequalities to infer its own hypothesis.

5. Now `x=F+1+(y+1)u0` forces `u0>=0` (otherwise `x<=F-y<0`), hence
   `x>=F+1>=2`. The last endpoint gives `x>=2+(t+1)y` exactly as in the
   strict-budget proof.

6. The `F^2+t` and `y+1` indices are positive. Their positive-base power
   requests force their abscissas canonical. The derived-label polynomial
   h is nonnegative on the recovered nonnegative representatives; the
   anchor has already excluded h=0. Its positive-base power request
   therefore forces its abscissa canonical as well.

At this point all fourteen pairs have precisely the canonical values used
by the original orientation-first proof. The remainder-sign recovery,
factorial fixed point, strict budget, digit ranges, Horn decoding and C222
calibration proceed unchanged. Zero global representatives are handled by
the original corrected `max(1,a)` argument; this proof does not require
restoring nonnegative shifted coordinates.

## 5. Compatibility with the proposed deterministic comparison center

Assume the parent agent's replacement

    D=A+(1-A)H^2,
    J=C^2(2e+1),
    H^2-(A^2-1)J^2=1,
    S^2-(D^2-1)R^2=1,
    S=U+Hg,   R=h+Cq.

The identity `D=1-(A-1)(A^2-1)J^2` gives `D=1 mod C`, while the
definition gives `D=A mod H`. It also gives `|D|>1` for `|A|>=2`,
`J!=0`. The inherited abscissa-residue lemma and `C^2|J` therefore yield
`i=+/-h mod |C|`, where `|C|=Y_i(|A|)`.

If `i>=2`, induction from `Y_2(a)=2a` gives

    Y_i(a) >= i+2a-2.

Since `a>W^W`, this gives `i+|h|<|C|`; consequently the congruence forces
`i=|h|<W`. All other indices are smaller by the squared cap.

If `i=1`, then `|C|=1`. The unchanged squared cap

    C^2=h^2+1+sum_nonanchor Y_i^2+u^2+v^2+w(w+1)

forces `h=0` and all nonanchor ordinates zero. All actual indices are then
0 except the anchor's 1, so they are independently below W. Apply the new
pool's finite-alphabet argument: its small nonnegative error includes the
anchor contribution `(+-1-0)^2=1`, is strictly below `|A-1|`, and cannot
be divisible by `A-1`. This excludes the exceptional branch without any
orientation premise and hence without circularity.

Completeness retains the prior choice of an even dominant h, a positive
main A, and the auxiliary index `l=hC`. The old unit-power calculation
gives the odd integer `J/C^2`, independently of the parity of A. Choose
the comparison pair as `X_h(D),Y_h(D)`. Its two needed congruences hold
because D has the two polynomial residue properties above. Thus the
weaker modulus C is enough, and there is no auxiliary CRT choice or
oddness condition on A to add.

## 6. Exact change to the current 282-variable centered parent

File:
`direct/strict_dimension_centered/equation.json` in Cofinal Anchors.

The pool is residual number 176 (zero-based), label
`cap.pooled_index_residue`. All fourteen abscissa coordinates are shifted
by +1 relative to their actual X values. Their coordinate numbers are

    155,164,171,177,181,185,189,193,197,201,205,209,213,217.

Delete the fourteen monomials `z_i^2` at those coordinates and add
`-z_i` only at

    171,177,181,185,189,197,201,209,213.

Those are precisely index3, index5, index6, index7, index8, index10,
index11, index13, and index14, the nine CRT representatives. The private
quotient is coordinate 236, and the actual divisor is `A-1=z151`.

Direct exact expansion gives the following before any other change:

| Pool | Variables | Rows | Degree | Monomials | Coefficient height | Coefficient L1 norm |
|---|---:|---:|---:|---:|---:|---:|
| Original squared fourteen |282|192|4|5491|128446|4087605|
| Linear fourteen |282|192|4|5491|128446|4087549|
| Linear nine |282|192|4|5216|128446|4086834|

These are achieved finite measurements, not a global complexity claim.
They show why merely changing every square to a linear term does not
reduce support after the outer sum of squares: the selective removal of
five unnecessary orientations is the useful part of this composition.

Both old and new solvability have the same semantic front. Given either
set of canonical pairs, all abscissa and ordinate error terms are divisible
by A-1. The unrestricted private pool quotient can therefore be changed
to the quotient required by the other presentation. This is an existence
equivalence, not an equality of the two quartic polynomials.
