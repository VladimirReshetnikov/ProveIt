# Even indices remove the small-ordinate branch

Working proof, 24 October 2026. This note is an internal research artifact;
it does not yet claim a complete transformed ZFC polynomial. No numerical
variable or term count is claimed here.

## 1. Chebyshev residue parity

For an integer a >= 2 put D=a^2-1 and alpha=a+sqrt(D), and define

    alpha^n = chi_a(n) + psi_a(n)*sqrt(D).

Thus chi_a(0)=1, chi_a(1)=a and
chi_a(n+1)=2a chi_a(n)-chi_a(n-1). Both coordinates are integers.

**Lemma 1.** If h>=1, j>=0 and

    chi_a(j) == +a or -a (mod chi_a(h)),

then j is odd.

**Proof.** Write u=chi_a(h), v=psi_a(h). The doubling identities give

    alpha^(2h) = 2u^2-1 + 2uv sqrt(D) == -1 (mod u)

in the quadratic ring Z[sqrt(D)]/(u). Reduce j modulo 2h, then reflect
the remainder about h when necessary. Since alpha is a unit and its
inverse is a-sqrt(D), the rational coordinate of alpha^(-r) is chi_a(r).
The result is

    chi_a(j) == +/-chi_a(r) (mod u),
    0 <= r <= h,  r == j (mod 2).

For h=1, the residue at r=0 is 1, which is not 0 modulo a; only r=1
can have residue +/-a modulo a. Hence j is odd.

For h>=2, strict monotonicity gives chi_a(h-2)<chi_a(h-1), and the
recurrence gives

    u-chi_a(h-1)
      = (2a-1)chi_a(h-1)-chi_a(h-2)
      > (2a-2)chi_a(h-1) >= 2a > a.

Consequently chi_a(h-1)<u-a and u>a. The case r=h has residue zero
and is impossible. For r<h, both chi_a(r) and a lie strictly between
0 and u, and chi_a(r)<u-a. The congruence chi_a(r)==+/-a (mod u)
therefore forces chi_a(r)=a. Strict monotonicity forces r=1. Again j
is odd. QED.

## 2. The signed even-index exclusion

**Lemma 2.** Let A,U,V,B,X,Y,S,R,k be integers. Suppose

    |A| >= 2, V != 0,
    U^2-(A^2-1)V^2 = 1,
    B == A (mod U), B odd,
    X^2-(A^2-1)Y^2 = 1,
    S^2-(B^2-1)R^2 = 1,
    S == X (mod U),
    R == 2k (mod 4Y).

Then |Y| != 1. Congruence notation can be read as the existence of
ordinary integer quotient witnesses, so the statement itself is entirely
polynomial in the usual way. Its proof only uses the last congruence
when Y=+/-1.

**Proof.** Set a=|A|. Classification of solutions of the Pell equation
for D=a^2-1 gives

    |U| = chi_a(h), |V| = psi_a(h), h>=1.

Here a+sqrt(a^2-1) is the least positive nontrivial integral norm-one
unit: the least nonzero positive ordinate is 1, with abscissa a. The
usual reduction by this unit proves the quoted classification directly.

The odd integer B cannot be +/-1. Indeed U would divide A-1 or A+1.
For h=1, |U|=a, which cannot divide either a-1 or a+1. For h>=2,
|U|>=2a^2-1>a+1, and both A+/-1 are nonzero of smaller magnitude.
Thus |B|>=3 and its auxiliary Pell equation is nonsingular.

Suppose |Y|=1. The main norm gives X=+/-A. By the same Pell
classification, for some j>=0 one has

    S = +/-chi_B(j), R = +/-psi_B(j).

This notation is valid for negative B too, since
chi_(-b)(j)=(-1)^j chi_b(j) and
psi_(-b)(j)=(-1)^(j-1) psi_b(j), with the zero-index convention.
The recurrence makes chi_B(j) an integer polynomial in B. Therefore
B==A (mod U) and S==X (mod U) imply

    chi_a(j) == +/-a (mod |U|).

Lemma 1 forces j odd. Since B is odd, the recurrence for psi_B
gives psi_B(j)==j (mod 2), so R is odd. But |Y|=1 and the last
congruence force R to be even. Contradiction. QED.

The hypothesis V!=0 is essential for this proof; a shared certificate
must supply it independently. In the current direct packet it is
supplied by the retained strict guard V>=1.

## 3. Restoring the size condition without its guard

**Lemma 3 (zero-ordinate exclusion).** In Lemma 2, additionally assume
1<=k and 2k<a=|A|. Then Y!=0.

**Proof.** The same common Pell classification gives u=|U|=chi_a(h)
with h>=1. Every nonzero integer B==A (mod U) has |B|>=a: for h=1,
u=a and B is a nonzero multiple of a; for h>=2, u>=2a^2-1>2a, and
the least magnitude in either residue class +/-a modulo u is a. Here
B is odd, so is nonzero.

If Y=0, the quotient form of the last congruence gives R=2k exactly.
This is a positive even integer, so its auxiliary Pell index cannot be
0 (ordinate zero) or 1 (ordinate of magnitude one). The index is at
least two, hence

    2k=|R| >= psi_|B|(2)=2|B| >= 2a,

contrary to 2k<a. QED.

Together Lemmas 2 and 3 give |Y|>=2. The main Pell classification now
has index at least two, hence

    |Y| >= psi_a(2) = 2a.

If 0<2k<W and a>W^2, all the additional hypotheses of Lemma 3 hold,
and |Y|>2k. Thus the ordinary signed index
theorem can be applied at the **even** requested index 2k without any
nonnegativity premise on a separately supplied Y-2k coordinate.

The sign of Y is not assumed. The signed comparison-base theorem is
applied to |Y| first; the usual small-residue argument with a positive
supporting power base fixes the actual signs afterwards.

## 4. A compiler transformation to test

For every power call m=n^k (with m>=0, n>=0 and k>=1), request instead

    m^2 = n^(2k).

The reverse implication is exact because both m and n^k are nonnegative.
Every shared seed index is even. Keep all initial non-index sign premises
and the strict common V guard. Delete only the separate seed-index
nonnegativity guards once the previous sections' prerequisites have been
checked. Then:

* In each index congruence, replace k by 2k. This changes a scalar
  coefficient only and does not increase the quadratic degree.
* In each final power-congruence residual
  X+nY-AY-m-Tq, replace m by m^2. The residual remains quadratic.
* Use a positive frame W bounding every n, 2k and m^2. A direct quadratic
  row W=C+sum(n)+sum(2k)+sum(m^2), with C>=1, suffices. Intermediate
  sum gates are optional, so output squaring has no inherent witness
  cost. The source's actual existing frame and any other required inputs
  must be retained in the new bound.
* Soundness first reconstructs the arithmetic meanings of the unchanged
  front outputs m. It then invokes the existing front-to-refutation
  theorem, or rebuilds a fresh old shared certificate by completeness.
  There is no pointwise assertion that the new Pell coordinates already
  solve the old-index equations.
* Completeness starts with the original front arithmetic data, selects
  the enlarged positive frame, and constructs fresh synchronized Pell
  witnesses at the indices 2k. Old Pell coordinates need not be retained.

### Literal rewrite of the supplied raw graph

The raw packet at `direct-work/reference/research/factorial-radius-output-sign-profile/raw/parent.json`
has 1,259 body variables and 1,177 body rows. Its 21 output coordinates
are

    6,93,104,106,113,532,533,546,547,560,573,
    574,583,591,599,607,608,617,625,626,635.

Each final `pow*.power_congruence` is preceded by an addition row
`z-m-AY=0`. Changing that row to `z-m^2-AY=0` needs no new variable
and keeps its degree at two. Likewise the index-congruence precursor
`z-k-4Yq=0` becomes `z-2k-4Yq=0`.

The final frame chain occupies rows 1134 through 1175. Replace the
contribution of each listed output m by m^2, and replace its endpoint
row 1176, `W-last=0`, by `W-2last=0`. All original frame summands were
nonnegative and the constant margin was positive; m^2>=m for every
nonnegative integer m. The resulting W therefore bounds every original
n and m, every new output m^2, and every doubled index 2k, strictly.
Each changed addition row is still a quadratic monic definition. This
description supplies a prototype strategy, not a certified transformed
artifact; the producer must identify each actual row and validate the
complete substitutions.

The retained strict common V guard also directly excludes Y=0 in this
graph: source rows 1117 through 1133 state that V is a product of all
15 distinct seed ordinates squared, multiplied by an integer. V>=1
forces every factor to be nonzero and gives Y^2|V. This is polynomial
algebra before any index interpretation. Lemma 3 provides a separate
exclusion that does not use this particular product implementation.

The 75-predicate starting domain has eleven scalar guards on surviving
index slacks and one predicate on a pair of index slacks. The doubling
argument is intended to remove these twelve predicates, retaining the
factorial lower bound and every non-index initial sign premise. The
associated twelve triples are private. This logical count is not yet a
claim about a projected polynomial's actual variable count.

No full metric should be inferred by subtracting guard counts alone.
The transformed literal rows, projection, coefficient expansion,
completeness order and pre-index hypotheses all need checking.

## 5. Finite diagnostic already performed

The congruence parity of Lemma 1 was checked in 216,000 cases:
2<=a<20, 1<=h<25, 0<=j<500. This is a transcription diagnostic;
the proof in Section 1 establishes the universal statement.
