import GowersSzemeredi.Definitions

/-!
# Gowers (2001), Sections 8--9: formal statements

The results below are `Prop`-valued definitions.  They formalize the statements
without asserting them and without adding axioms to Lean's environment.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Section 8: Progressions of length four -/

/-- Translation of a finite subset of `ZMod N`. -/
noncomputable def translate {N : Nat} (A : Finset (ZMod N)) (s : ZMod N) :
    Finset (ZMod N) := by
  classical
  exact A.image fun x => x + s

/-- **Proposition 8.1.** A linearly varying large Fourier coefficient of the
first differences produces quadratic phase bias on translates of `P`. -/
def proposition_8_1 : Prop :=
  forall (N : Nat) [NeZero N] (_hNodd : Odd N)
      (A : Finset (ZMod N)) (P : ModAP N)
      (beta : Real),
    (exists lambda mu : ZMod N,
      beta * (N : Real) ^ 2 * P.carrier.card <=
        ∑ k ∈ P.carrier,
          ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2) ->
    exists psi : ZMod N -> ZMod N -> ZMod N,
      (forall s, PolynomialOn 2 Finset.univ (psi s)) /\
      beta * N * P.carrier.card / Real.sqrt 2 <=
        ∑ s : ZMod N,
          ‖∑ z ∈ translate P.carrier s,
            balanced A z * exponential (-(psi s z))‖

/-- **Theorem 8.2.** The quantitative length-four case. -/
def theorem_8_2 : Prop :=
  exists C : Real, 0 < C /\ forall (N : Nat) [NeZero N] [Fact N.Prime]
      (A : Finset (ZMod N)) (delta : Real),
    0 < delta -> (A.card : Real) = delta * N ->
    Real.exp (Real.exp ((1 / delta) ^ C)) <= N -> HasModAP A 4

/-- **Corollary 8.3.** The equivalent coloring formulation. -/
def corollary_8_3 : Prop :=
  exists c : Real, 0 < c /\ forall (N r : Nat), 0 < r ->
    (r : Real) <= (Real.log (Real.log N)) ^ c ->
    forall color : Nat -> Fin r, HasMonochromaticAP N r color 4

/-! ## Section 9: Obtaining approximate homomorphisms -/

/-- **Lemma 9.1.** The interpolation inequality used to pass from fourth to
sixteenth Fourier moments. -/
def lemma_9_1 : Prop :=
  forall (n : Nat) (a : Fin n -> Real), (forall i, 0 <= a i) ->
    (∑ i, (a i) ^ 4) <=
      (∑ i, (a i) ^ 2) ^ ((6 : Real) / 7) *
        (∑ i, (a i) ^ 16) ^ ((1 : Real) / 7)

/-- **Lemma 9.2.** A `gamma`-additive function respects many additive
sixteen-tuples.  Membership in `B`, omitted by the OCR sentence, is explicit. -/
def lemma_9_2 : Prop :=
  forall (N : Nat) [NeZero N] (B : Finset (ZMod N))
      (phi : ZMod N -> ZMod N) (gamma : Real),
    GammaAdditive B phi gamma ->
    gamma ^ 7 * (N : Real) ^ 15 <= phiAdditiveTupleCount 8 B phi

/-- **Lemma 9.3.** A random restriction upgrades a positive proportion of
respected 8-relations to an approximate homomorphism of order eight. -/
def lemma_9_3 : Prop :=
  forall (alpha beta eta : Real), 0 < alpha -> 0 < beta -> 0 < eta ->
    exists N0 : Nat, forall (N : Nat) [NeZero N], N0 <= N ->
      forall (B : Finset (ZMod N)) (phi : ZMod N -> ZMod N),
        (B.card : Real) = beta * N ->
        alpha * beta ^ 15 * (N : Real) ^ 15 <= phiAdditiveTupleCount 8 B phi ->
        exists B' : Finset (ZMod N), B' ⊆ B /\
          (alpha * eta / 4) ^ ((2 : Nat) ^ 19) * beta ^ 15 * (N : Real) ^ 15 <=
            additiveTupleCount 8 B' /\
          GammaHomOfOrder 8 B' phi (1 - eta)

/-- **Corollary 9.4.** The combination of Lemmas 9.2 and 9.3.  The printed
statement inherits the latter's sufficiently-large-`N` proviso; it is made
explicit here. -/
def corollary_9_4 : Prop :=
  forall (beta gamma eta : Real), 0 < beta -> 0 < gamma -> 0 < eta ->
    exists N0 : Nat, forall (N : Nat) [NeZero N], N0 <= N ->
      forall (B : Finset (ZMod N)) (phi : ZMod N -> ZMod N),
        (B.card : Real) = beta * N -> GammaAdditive B phi (gamma * beta ^ 3) ->
        exists B' : Finset (ZMod N), B' ⊆ B /\
          (gamma ^ 7 * beta ^ 6 * eta / 4) ^ ((2 : Nat) ^ 19) *
              beta ^ 15 * (N : Real) ^ 15 <= additiveTupleCount 8 B' /\
          GammaHomOfOrder 8 B' phi (1 - eta)

end LeanProofs.GowersSzemeredi
