import GowersSzemeredi.Section10

/-! Regular components with complementary error exponents. Choosing t=1/2
recovers the original square-root clause of Lemma 10.5. Choosing t=1/5
recovers the variant needed for Lemma 10.6. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- All six component conclusions, with exceptional proportion 5*eta^t
and pointwise error bound 300*eta^(1-t). -/
def IsSection10RegularComponentAt {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N)) (x : X)
    (alpha eta rho : Real) (M N0 : Nat) (t : Real) (W : Finset X) : Prop :=
  D.FibreSaturated W /\
    VariesByFactorAtMostTwo W (fun y => domainDifferenceWeight D x y) /\
    AlmostEvery (1 - 5 * eta ^ t) W
      (fun y => domainProportionateError D phi B x y <=
        300 * eta ^ (1 - t)) /\
    rho ^ 2 * alpha ^ 2 * M * N0 / 16 <= W.card /\
    VariesByFactorAtMostTwo W D.fibreSize /\
    (forall y, y ∈ W -> alpha ^ 2 * M / 16 <= D.fibreSize y) /\
    forall d, d ∈ B -> (1 - eta) * W.card <= (W ∩ D.shift W d).card

/-- One component simultaneously supports every complementary exponent pair. -/
def lemma_10_5_all_tradeoffs : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat) (sigma eta : Real)
      (x : X),
    Section10Setup D phi B alpha M sigma eta ->
    sigma <= eta * alpha ^ 2 -> IsSection10Anchor D phi B alpha M N eta x ->
    0 < rho -> rho <= alpha / 192 -> rho <= alpha ^ 2 / 32 ->
    sigma <= eta * rho ^ 4 * alpha / 384 ->
      exists W : Finset X,
        ∀ t : Real, IsSection10RegularComponentAt D phi B x alpha eta rho M N t W

/-- The original square-root trade-off, with the proof's inherited setup explicit. -/
def lemma_10_5_original_sqrt : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat) (sigma eta : Real)
      (x : X),
    Section10Setup D phi B alpha M sigma eta ->
    sigma <= eta * alpha ^ 2 -> IsSection10Anchor D phi B alpha M N eta x ->
    0 < rho -> rho <= alpha / 192 -> rho <= alpha ^ 2 / 32 ->
    sigma <= eta * rho ^ 4 * alpha / 384 ->
      exists W : Finset X,
        IsSection10RegularComponentAt D phi B x alpha eta rho M N (1 / 2) W

end LeanProofs.GowersSzemeredi
