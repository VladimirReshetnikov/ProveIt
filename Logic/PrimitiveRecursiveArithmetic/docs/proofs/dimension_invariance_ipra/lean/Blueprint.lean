/-!
# Constructive dimension invariance: Lean development blueprint

STATUS: UNFINISHED FORMALIZATION OUTLINE. This file contains documentation
only. All proposed declarations below are inside this block comment. None is
an axiom, an admitted theorem, an executable proof, or a declaration which has
been checked against Lean. No Lean compiler was available for this delivery.
In particular, this file does not establish the main theorem in Lean.

Inspected upstream baseline
--------------------------

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: daade0300022828cdba33a324d987997fee9fa08
Lean and mathlib: v4.32.0, from the root lean-toolchain and lakefile.toml.
Existing namespace: LeanProofs.ConciseIPRA.

Verified source paths, relative to the repository root:

  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/TeqReflect.lean
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/TeqPair.lean
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/TeqRec.lean
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean

The first stage below is finite mathematics in the Lean metatheory. The
second stage builds an actual derivation in the embedded first-order iPRA.
The first stage alone must not be reported as formalization "in iPRA".

======================================================================
I. Exact finite theorem and data representations
======================================================================

Use the natural-number codings in the article for the eventual arithmetic
statement. For readable host-Lean specifications, use the following proposed
types. Their names are local design choices, not existing upstream APIs.

  abbrev Grid (d N : Nat) := Fin d -> Fin (N + 1)
  abbrev QVector (m : Nat) := Fin m -> Rat
  abbrev GridTable (d m N : Nat) := Grid d N -> QVector m

Store a GridTable as a finite list indexed in mixed radix N+1 in the coded
version. Signed numerators and positive denominators code rationals; clear
positive denominators for all comparisons. The norm of a vector with no
coordinates is zero. All maxima are finite folds, initialized at zero.

  def qdist (a b : QVector m) : Rat := max_j |a j - b j|

The notation max_j is explanatory, not Lean syntax. Implement it using a
finite fold and prove: qdist is nonnegative; each coordinate difference is
bounded by it; and a nonempty coordinate maximum is attained by a least
bounded index. No decidability of arbitrary real equality is involved.

A Kuhn d-simplex has a base k with k_j < N and a permutation p of 0,...,d-1.
Its vertices are

  v_t = k + sum_{s < t} e_{p(s)},             0 <= t <= d.

For d=0 there is one empty base and one empty permutation. For N>=1 there
are exactly N^d * d! top-dimensional simplices, so every simplex enumeration
and witness search has an explicit primitive-recursive bound.

  structure KuhnSimplex (d N : Nat) where
    base : Fin d -> Fin N
    perm : Equiv.Perm (Fin d)

  def KuhnSimplex.vertex (s : KuhnSimplex d N)
      (t : Fin (d + 1)) : Grid d N := ...

For the natural-number implementation, enumerate permutations by filtering
all d-tuples with entries <d for distinctness; this deliberately simple
bound d^d avoids reliance on an unbounded enumeration procedure. The number
d! may be used for sharper complexity statements after correctness is proved.

  def OppositeSeparated (F : GridTable d m N) (delta : Rat) : Prop :=
    forall (i : Fin d) (u v : Grid d N),
      u i = 0 -> v i = N -> delta <= qdist (F u) (F v)

  def SimplexSmall (F : GridTable d m N) (delta : Rat) : Prop :=
    forall (s : KuhnSimplex d N) (a b : Fin (d + 1)),
      (d : Rat) * qdist (F (s.vertex a)) (F (s.vertex b)) < delta

The second formulation avoids a division in the arithmetic input predicate.
For d>0 it is equivalent to simplex image diameter < delta/d. The universal
quantifiers in these host-Lean specifications range over finite enumerations;
their coded predicates are primitive-recursive Boolean scans.

  theorem finite_dimension_obstruction
      (d m N : Nat) (hN : 0 < N) (delta : Rat) (hdelta : 0 < delta)
      (F : GridTable d m N)
      (hsep : OppositeSeparated F delta)
      (hsmall : SimplexSmall F delta) : d <= m := ...

Handle d=0 directly. The substantive proof below assumes 0<d. The case m=0
is included: if d>0, separated opposite faces already contradict qdist=0.

======================================================================
II. Finite cubical Sperner theorem
======================================================================

Labels are 0,...,d. Coordinates here are indexed 0,...,d-1. The correct
boundary conditions are deliberately recorded in full:

  LOWER i-face: u_i = 0  implies label(u) <= i.
  UPPER i-face: u_i = N  implies label(u) != i.

  def CubicallyAdmissible (L : Grid d N -> Fin (d + 1)) : Prop :=
    (forall i u, u i = 0 -> (L u).val <= i.val) /\
    (forall i u, u i = N -> (L u).val != i.val)

  def Rainbow (L : Grid d N -> Fin (d + 1))
      (s : KuhnSimplex d N) : Prop :=
    forall color : Fin (d + 1),
      exists t : Fin (d + 1), L (s.vertex t) = color

Prove the stronger parity statement: the number of rainbow top simplices is
odd. A least rainbow simplex is then obtained by bounded search.

  theorem cubical_sperner_odd (hN : 0 < N)
      (hL : CubicallyAdmissible L) :
      rainbowCount L % 2 = 1 := ...

  def findRainbow (...) : Nat := boundedLeast ...
  theorem findRainbow_spec (...) : Rainbow L (decodeSimplex (findRainbow ...)) := ...

Detailed finite proof obligations:

1. Enumerate incidence records (s,t), where t=0,...,r is the vertex omitted
   from a Kuhn r-simplex. A record is good if its r retained vertices carry
   each label 0,...,r-1 exactly once.

2. Within one r-simplex the parity of the number of good records equals the
   indicator that the simplex is rainbow. Indeed the count is 1 when the
   labels are 0,...,r; 2 when precisely the lower r labels occur with one
   repeat; and 0 in all other cases. Prove this by a bounded label histogram,
   with the r=0 parity base handled separately.

3. Pair the interior incidence records explicitly. Let p be the ordered
   list of coordinate directions of s and k its base.

   - If 0<t<r, swap p(t-1) and p(t), keep k and t unchanged.
   - If t=0 and k_{p(0)}+1<N, replace k by k+e_{p(0)}, rotate p left,
     and set the omitted vertex to r.
   - If t=r and k_{p(r-1)}>0, replace k by k-e_{p(r-1)}, rotate p right,
     and set the omitted vertex to 0.

   Prove the mate operation preserves the retained ordered vertex set up to
   permutation, is an involution, and has no fixed point. The unpaired
   t=0 records lie on upper faces; the unpaired t=r records lie on lower
   faces. This avoids an appeal to geometric manifold theory or a generic
   triangulation package.

4. Good records on every upper i-face are excluded because label i is
   forbidden. A good record on a lower i-face with i<r-1 is excluded
   because every label is <=i, so label r-1 cannot occur. The only possible
   good exterior records are on the last lower face. Their explicit
   bijection with the rainbow (r-1)-simplices of that face yields

       rainbowCount_r mod 2 = rainbowCount_(r-1) mod 2.

5. For the iPRA derivation, do not induct on the statement "for every
   labeling in dimension r". Fix the original full table L and form its
   nested restrictions to the faces whose final d-r coordinates are zero.
   For r<d, the original lower r-face condition ensures labels <=r on this
   restriction. Each restricted labeling has exactly the lower/upper
   conditions needed in dimension r. Induct on r on the equation

       parity(r, fixed_full_table_L) = 1,

   using a guard r<=d if needed. This is a quantifier-free invariant of
   fixed primitive-recursive scans. The r=0 face is the single origin,
   whose label is 0, so its rainbow count is 1. This is the needed
   arithmetic-strength audit, not merely a statement that the proof is
   finite.

======================================================================
III. Staggered cells and first-zero coloring
======================================================================

Assume d>0 and delta>0. For each source coordinate i=0,...,d-1 define the
shifted target cell of a grid vertex u by the m-tuple of integers

  cell_i(u)_j = floor(F(u)_j / delta - i/d).

Implement floor on a signed rational by Euclidean integer division. Prove
its interval characterization and the following exact rational lemma:

  floor(a)=floor(b) -> |a-b|<1.

Define a bit by a bounded search over the entire NEGATIVE i-face:

  bit_i(u)=0 iff there is v in the source grid with v_i=0 and
                         cell_i(v)=cell_i(u).
  bit_i(u)=1 otherwise.

This is a finite characteristic function, not an undecidable test about
whether the image of a continuum meets a cell. A witness of bit_i=0 may be
the least face vertex returned by its bounded scan.

  lemma bit_lower (u_i=0) : bit_i(u)=0 := ...

The witness is u itself.

  lemma bit_upper (u_i=N) : bit_i(u)=1 := ...

If the bit were zero, take its finite face witness v. Equal cell coordinates
give |F(u)_j-F(v)_j|<delta for every j, hence qdist(F(u),F(v))<delta. This
contradicts hsep. Treat the empty target dimension separately when proving
the strict maximum statement; its distance is zero and delta>0.

Color a vertex by its FIRST zero bit, or d if there are no zero bits:

  label(u) = least i<d with bit_i(u)=0, if such i exists;
             d, otherwise.

The search is bounded by d. The witness bit_i=0 on a lower i-face implies
label(u)<=i. On an upper i-face bit_i=1 excludes label(u)=i. Therefore this
labeling is CubicallyAdmissible, and Section II gives a rainbow simplex.

Choose its vertices w_0,...,w_d by their distinct labels. This selection is
another bounded search over d+1 vertices; no choice principle is required.
Then

  bit_i(w_i)=0,            bit_i(w_d)=1,             for every i<d.

Consequently cell_i(w_i) and cell_i(w_d) are different. Let j_i<m be the
least coordinate on which they differ. If m=0 no such difference is
possible, giving the immediate contradiction noted above.

======================================================================
IV. The target coordinates j_i are distinct
======================================================================

For fixed i let a=F(w_i)_{j_i}/delta and b=F(w_d)_{j_i}/delta.
The two integer floors of a-i/d and b-i/d differ. Set

  k_i = min(floor(a-i/d), floor(b-i/d)) + 1,
  theta_i = k_i + i/d.

The exact crossing lemma is

  min(a,b) < theta_i <= max(a,b).

For each target coordinate j, let A_j and B_j be the minimum and maximum
of the normalized coordinate values F(w_t)_j/delta over t=0,...,d. The
simplex smallness hypothesis gives

  B_j - A_j < 1/d.

If j_i=j_h, both thresholds lie in (A_j,B_j]. If i!=h with 0<=i,h<d,

  d*theta_i=d*k_i+i,       d*theta_h=d*k_h+h

are DISTINCT integers, since equality would equate two different residues
modulo d. Distinct integers are separated by at least one, so

  |theta_i-theta_h| >= 1/d.

This contradicts the preceding strict width bound. Thus i -> j_i is an
injection Fin d -> Fin m. A finite pigeonhole/counting lemma gives d<=m.

Proposed intermediate host-Lean statements:

  lemma differing_floor_crossing (...) :
    min a b < theta /\ theta <= max a b := ...

  lemma staggered_threshold_separation
      (hd : 0<d) (i h : Fin d) (hih : i!=h) (k l : Int) :
      1 <= |(d : Rat) * ((k : Rat)+(i.val : Rat)/d
                                   - (l : Rat)-(h.val : Rat)/d)| := ...

  theorem selected_coordinate_injective (...) :
      Function.Injective selectedCoordinate := ...

Prove pigeonhole by finite histograms or elimination on a coded injection.
An arbitrary host-Lean cardinality theorem is useful for cross-checking,
but its use does not itself supply the object-language iPRA derivation.

======================================================================
V. Coding and the object-language endpoint
======================================================================

First define fixed primitive-recursive symbols for:

  integer/rational encodings; list/tuple lookup; integer division and floor;
  finite minimum/maximum; source grid enumeration; permutation enumeration;
  vertex construction; face membership; incidence mate; histogram/parity;
  positive-rational comparison; opposite-face separation scan; simplex
  smallness scan; shifted-cell table; bit and label tables; least rainbow
  simplex; color-selected vertices; selected target coordinates; and the
  relevant code-size/loop bounds.

Supply validity guards (positive denominators, correct tuple lengths, and
table sizes) in every coded input predicate. Malformed codes are rejected.
The arithmetic statement uses natural-number variables for all inputs:

  forall d m N deltaCode tableCode,
    FiniteHyp(d,m,N,deltaCode,tableCode)=1 -> d<=m.

Here FiniteHyp incorporates N>0, delta>0, table validity, separation, and
simplex smallness. A relation such as d<=m is represented by a fixed
primitive-recursive comparison characteristic term. The entire matrix is
quantifier-free. This is a uniform theorem about finite numerical data.

Every loop is implemented by the fixed PR syntax of ConciseIPRA.PR; do not
use an alleged primitive-recursive universal evaluator of arbitrary PR
program codes. The fact that PR is an inductive datatype in Lean does not
make such an evaluator primitive recursive in arithmetic.

After proving the host-Lean statements as a design check, construct their
object-language counterparts. The exact existing interfaces are:

  import ConciseIPRA.PR
  import ConciseIPRA.NativeBiInterpretation
  namespace LeanProofs.ConciseIPRA
  open Syn
  open scoped Fm

  -- PROPOSED, NOT IMPLEMENTED:
  def finiteDimensionFormula : Fm PTm 0 := ...

  theorem finite_dimension_ipra :
      ([] : List (Fm PTm 0)) ⊢[PRAAx] finiteDimensionFormula := ...

PRA.qfInd is verified upstream and accepts only an explicitly quantifier-free
formula. Deduction.Prf supplies intuitionistic first-order rules. For the
small native scalar calculus the existing bridge is exactly:

  pra_iff_native :
    (Gamma ⊢[PRAAx] phi) <->
      NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi).

Thus, once the preceding object theorem exists, the native endpoint is:

  theorem finite_dimension_native :
      NPrf [] (NFm.ofPRA finiteDimensionFormula) :=
    (pra_iff_native).mp finite_dimension_ipra

That last declaration is still a proposed endpoint, since its new formula
and its iPRA proof have not been implemented in this delivery.

The existing TeqReflect and TeqRec modules give an alternative route through
the scalar theory: characteristic-term reflection of quantifier-free
formulas, quantifier-free induction from equation induction, and compilation
of primitive recursion by a paired accumulator. Existing interpretation
theorems then transfer the resulting derivations to PRAAx and NPrf.

======================================================================
VI. Quantitative maps and dimension invariance
======================================================================

The analytic-facing wrapper is separate from the finite theorem. For a map
on a cube, provide rational approximation evaluators, an explicit uniform
modulus of continuity, and a positive separation bound for opposite faces.
Choose a finite grid and precision so the rational table F satisfies the
two exact inequalities above. In particular, errors must leave room for the
STRICT simplex diameter bound. Record the choice formula, not an unbounded
"refine until small" procedure.

For a quantitatively presented homeomorphism, the inverse modulus gives the
opposite-face separation, and the forward modulus gives the small-simplex
condition. Apply the finite theorem in each direction to obtain d<=m and
m<=d, hence d=m. A compact restriction or local box must have all necessary
domain, range, and modulus data supplied; do not extract these by an
unexplained appeal to classical compactness.

For fixed primitive-recursive evaluators and moduli this is a theorem
schema in iPRA. First-order iPRA does not quantify over arbitrary functions
R^d -> R^m. A separate higher-order/oracle reading may be discussed, but
must not be silently identified with the first-order arithmetic theorem.

======================================================================
VII. Completion gates
======================================================================

1. Compile concrete coding and finite combinatorial modules with upstream
   Lean/mathlib v4.32.0; test small finite inputs as implementation checks.
2. Complete incidence pairing and cubical parity, including d=0, d=1,
   N=1, empty target dimension, and all boundary cases.
3. Complete rational cell, threshold separation, and finite injection lemmas.
4. Complete all PR-symbol definitions and their object-language arithmetic
   derivations, keeping every induction invariant quantifier-free.
5. Construct finite_dimension_ipra; only then apply pra_iff_native.
6. Prove the explicitly quantitative table-extraction wrapper.
7. Audit generated declarations for admissions, new axioms, and unintended
   classical dependencies; distinguish host metatheory from object logic.

Current delivery status: all seven gates remain formalization work. The
accompanying article gives the human-readable mathematical proof; this file
identifies the exact Lean obligations and existing integration interfaces.
-/
