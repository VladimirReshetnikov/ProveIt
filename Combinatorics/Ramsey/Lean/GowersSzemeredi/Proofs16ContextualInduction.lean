import GowersSzemeredi.Proofs16CommonBaseAssembly
import GowersSzemeredi.Proofs16FinalSections
import GowersSzemeredi.Proofs16StructuredExtraction
import GowersSzemeredi.Proofs16InductionAssembly
import GowersSzemeredi.Proofs16LargePieceMass
import GowersSzemeredi.Proofs16BaseCaseEndpoint

/-! Historical conditional induction from the universal common-base lift.
Proofs16ContextualLiftCounterexample refutes this premise for every k>=1.
The conditional implications are preserved; the viable remaining obligation
is the existential selected-domain contract in Proofs16SelectedLiftInduction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The universal common-base lifting predicate, preserved unchanged.
Proofs16ContextualLiftCounterexample proves its negation for k>=1 with the
actual product property, structured pair, and complete common-base fields.
This definition asserts nothing and is not a proof of Lemma 16.10. -/
def Section16ContextualLiftAt (k : Nat) : Prop :=
  ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        HasProductProperty B phi gamma → Section16StructuredPair theta gamma B phi →
        ∀ D : Section16CommonBaseData theta gamma B phi,
          MultiplyLinearFunction gamma 1 (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
            (section16PhiOne phi D.x0)

/-- A supported relation has no more projected points than its support. -/
theorem RelationSupportedOn.projection_subset {N k : Nat}
    {Gamma : Finset (Point N k × ZMod N)} {H : Finset (Point N k)}
    (h : RelationSupportedOn Gamma H) : relationProjection Gamma ⊆ H := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  exact h z hz

/-- The structured-pair extraction, common-base construction, contextual
lift, and exact mass transport supply the required large-piece assertion. -/
theorem section16_large_piece_of_contextual_lift {k : Nat}
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16ContextualLiftAt k) (hk : 1 ≤ k) :
    Section16LargePieceAt (k + 1) := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨Ns, hNs⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  obtain ⟨Nc, hNc⟩ := (hth k hk le_rfl).common_base_data theta gamma ht ht1 hg hg1
  obtain ⟨Nl, hNl⟩ := hlift theta gamma ht ht1 hg hg1
  refine ⟨max 3 (max Ns (max Nc Nl)), fun N _ _ hN Gamma _hcard hprod hlarge => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNs' : Ns ≤ N := (le_max_left Ns _).trans ((le_max_right _ _).trans hN)
  have hNc' : Nc ≤ N := (le_max_left Nc Nl).trans
    ((le_max_right Ns _).trans ((le_max_right _ _).trans hN))
  have hNl' : Nl ≤ N := (le_max_right Nc Nl).trans
    ((le_max_right Ns _).trans ((le_max_right _ _).trans hN))
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  rcases hNs N hNs' ho Gamma hprod with hsmall | ⟨B, phi, hgraph, hstructured⟩
  · obtain ⟨H, hH, hsupp⟩ := hsmall
    have hp : ((relationProjection Gamma).card : Real) ≤ H.card :=
      Nat.cast_le.mpr (Finset.card_le_card hsupp.projection_subset)
    linarith
  · obtain ⟨D⟩ := hNc N hNc' B phi hstructured
    have hunit := hNl N hNl' B phi (hprod B phi hgraph) hstructured D
    exact section16_large_piece_of_common_base theta gamma ht ht1 hg hg1 Gamma B phi
      (D.H ∩ D.J) D.Y D.x0 hgraph D.good_mass hunit

/-- The exact fixed-dimension induction step, with the unresolved lifting
statement isolated and all other construction and iteration work proved. -/
theorem theorem_16_2_step_of_contextual_lift {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (hlift : Section16ContextualLiftAt k) : Theorem162At (k + 1) :=
  theorem_16_2_of_large_piece (section16_large_piece_of_contextual_lift hth hlift hk)

/-- All dimensions of Theorem 16.2 follow from the contextual lifting steps.
The proved zero- and one-dimensional bases are used directly. This is a
conditional theorem and is not counted as an exact companion. -/
theorem theorem_16_2_of_contextual_lifting
    (hlift : ∀ k : Nat, 1 ≤ k → Section16ContextualLiftAt k) : theorem_16_2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | k
    · exact theorem_16_2_zero
    · rcases k with _ | k
      · exact lemma_16_3_holds
      · apply theorem_16_2_step_of_contextual_lift (by omega)
        · intro l hl hlk
          exact ih l (by omega)
        · exact hlift (k + 1) (by omega)

end LeanProofs.GowersSzemeredi
