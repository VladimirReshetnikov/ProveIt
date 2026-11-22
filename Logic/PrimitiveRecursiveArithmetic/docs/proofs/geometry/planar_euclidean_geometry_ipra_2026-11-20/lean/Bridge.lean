import Translation
import Axioms

/-! Connect the executable point-to-scalar formula translation to incidence
    interpreted independently by an affine parameter on the closed interval. -/
namespace PlanarIPRA.Bridge

open PlaneTranslation
open Synthetic (Bet Cong distSq mix affine bet_iff_polyBet)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def affineGeometryAtom (ρ : Nat → Point K) : GAtom → Prop
  | .eq a b => ρ a = ρ b
  | .bet a p b => Bet (ρ a) (ρ p) (ρ b)
  | .cong a b c d => Cong (ρ a) (ρ b) (ρ c) (ρ d)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem distSq_eq_d2 (a b : Point K) : distSq a b = d2 a b := by
  unfold distSq d2
  ring

theorem affine_atom_correct (ρ : Nat → Point K) (atom : GAtom) :
    affineGeometryAtom ρ atom ↔ geomAtom ρ atom := by
  cases atom with
  | eq a b => rfl
  | bet a p b => exact bet_iff_polyBet _ _ _
  | cong a b c d =>
    change distSq (ρ a) (ρ b) = distSq (ρ c) (ρ d) ↔ _
    rw [distSq_eq_d2, distSq_eq_d2]
    rfl

private theorem models_agree (φ : Geom) (ρ : Nat → Point K) :
    holds affineGeometryAtom ρ φ ↔ holds geomAtom ρ φ := by
  induction φ generalizing ρ with
  | atom a => exact affine_atom_correct ρ a
  | bot => rfl
  | conj p q hp hq => exact and_congr (hp ρ) (hq ρ)
  | disj p q hp hq => exact or_congr (hp ρ) (hq ρ)
  | impl p q hp hq => exact imp_congr (hp ρ) (hq ρ)
  | ex i p hp => exact exists_congr (fun v => hp (assign ρ i v))
  | all i p hp => exact forall_congr' (fun v => hp (assign ρ i v))

theorem translate_from_affine (φ : Geom) (ρ : Nat → Point K) :
    holds affineGeometryAtom ρ φ ↔ holds scalarAtom (split ρ) (translate φ) :=
  (models_agree φ ρ).trans (translate_correct φ ρ)

/-- All A,P: if P lies between A and itself, then P=A. -/
def betIdentity : Geom :=
  .all 0 (.all 1 (.impl (.atom (.bet 0 1 0)) (.atom (.eq 1 0))))

theorem translated_betIdentity (ρ : Nat → Point K) :
    holds scalarAtom (split ρ) (translate betIdentity) := by
  apply (translate_from_affine betIdentity ρ).mp
  change ∀ A P : Point K, Bet A P A → P = A
  intro A P h
  obtain ⟨t, _, _, eqn⟩ := h
  rw [eqn]
  apply Prod.ext <;> dsimp [mix, affine] <;> ring

/-- Closed point sentence for Tarski's inner Pasch axiom. -/
def innerPaschSentence : Geom :=
  .all 0 (.all 1 (.all 2 (.all 3 (.all 4
    (.impl (.conj (.atom (.bet 0 3 2)) (.atom (.bet 1 4 2)))
           (.ex 5 (.conj (.atom (.bet 3 5 1)) (.atom (.bet 4 5 0)))))))))

theorem translated_innerPasch (ρ : Nat → Point K) :
    holds scalarAtom (split ρ) (translate innerPaschSentence) := by
  apply (translate_from_affine innerPaschSentence ρ).mp
  change ∀ A B C P Q : Point K, Bet A P C ∧ Bet B Q C →
    ∃ X : Point K, Bet P X B ∧ Bet Q X A
  rintro A B C P Q ⟨hp, hq⟩
  exact Synthetic.inner_pasch hp hq

end PlanarIPRA.Bridge
