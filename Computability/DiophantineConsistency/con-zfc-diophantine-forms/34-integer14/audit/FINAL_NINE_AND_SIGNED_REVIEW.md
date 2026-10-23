# Independent final mathematical audit

Reviewed the final nine-variable formulas and the signed fourteen- and
fifteen-variable formulas at the pinned source revision
8c6eec9d19ef80538c8e61ff6e0180040583446a.

## Nine variables

The universal majorants are valid on the entire prescribed nonnegative
outer domain, before imposing square conditions. The packed residue excludes
R=0. Hence |A|>=2, K>=1, J nonzero, D,F>=1, and AE>=0. For r>=2,
4R^2+2(r+1)R+r^2 is strictly positive even for real R: its minimum is
(3r^2-2r-1)/4>0. Thus RC+r^2>|RC|, with integer excess at least one.
The claimed MD bound follows. Likewise 2(j+1)C^2-2rC+r^2>=0 gives
TC>=|CH|. The MI bound follows from G=FDC+F-A(F-1),
|H|<=H^2 and |AH|<=A^2+H^2. These arguments include C=0, H=0,
and signed R,C,I.

The replacement Omega=um is sound. When m=0 the fourth power is nonzero
because Theta/u=n+M+v/u>=1. For m nonzero the factorization over complex
square roots implies integral roots: if their weighted sum is nonzero,
solve linearly for the roots; if zero, the V0 separation forces both
radicands to vanish. The resulting Z is an integer >=2M+1. Therefore
n+M+v/u=mZ forces m positive and u|v. Conversely the specified integer n
is at least two and makes a factor vanish. There is no unhandled zero
margin or negative-radicand branch.

The degree calculation in SIGNED_QUADRATIC_NINE_PROOF.md was independently
checked as polynomial identities, including DeltaD, DeltaF, DeltaIRoot,
DeltaI and the three-term telescoping difference of products. The leading
term of Delta is DeltaD MF^2 MI^2. The potentially competing term DF DeltaI
has the same L coefficient 24170 but constant degree 71 rather than 72.
The leading inner term is Omega^2 V0^2 Delta, degree 46162L+148 and
coefficient 2^96. The outer correction is lower degree. Thus the exact
result is 92324L+296 with coefficient 2^192. Matching upper bounds and a
nonzero diagonal leader justify total degree, not merely diagonal degree.

The independent census gives 1559 operations over nine nonnegative
variables and 1554 over nine positive variables. Both have 80 live
nonliteral fixed leaves. Coefficient recipes and their materialization
are separate from this operation model.

## Fourteen and fifteen unrestricted integers

The cofinal odd-power-of-two choice of b and canonical formula
w=2^(2R+1-k) justify square w. This is an existence construction, not
an assertion that every ratio witness is a square. The released h sign,
nonzero i, linear-prefix guard stack and signed-H product-Pell argument
are accepted as detailed in the other audit notes. The phi guard is
retained; no unsupported signed-C extension is used.

The final JSON DAGs independently certify exact leading monomials:

* signed14: degree 813056L+2152, leader
  2^832 * 12^120 * Bodd^(406528L+8), 1586 operations, 14 variables.
* signed15_linear: degree 406528L+2528, leader
  2^832 * 12^248, 1594 operations, 15 variables.

The independent checker propagates a formal Bodd exponent with an exact
integer leading coefficient. No modular specialization or guessed generic
coefficient supplies this degree assertion. It also checks all four final
circuit censuses by reachability from the output, not stored counts alone.

## Scope

The new proofs are mathematical and use the inherited constructive Jones,
Pell, compiler and machine-calibration interfaces. They are not newly
compiled Lean or Rocq certificates. The finite regressions supplement,
but do not replace, the universal proofs. No minimality claim is made.
