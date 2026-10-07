import OAI.Combinatorics.Progressions.Sampling.RationalForecastGridTail

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def outputAxisReindexAddEquiv {A B : Type*} (e : A ≃ B)
    (H : Type*) [AddCommGroup H] : (A → H) ≃+ (B → H) where
  toFun x b := x (e.symm b)
  invFun y a := y (e a)
  left_inv x := by funext a; simp
  right_inv y := by funext b; simp
  map_add' _ _ := rfl

@[simp] theorem outputAxisReindexAddEquiv_apply {A B H : Type*} [AddCommGroup H]
    (e : A ≃ B) (x : A → H) (b : B) :
    outputAxisReindexAddEquiv e H x b = x (e.symm b) := rfl

theorem rationalOutputDensity_axis_reindex {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) [NeZero N] (r : A → ZMod N) :
    rationalOutputDensity p Y N r =
      rationalOutputDensity p (fun ω b => Y ω (e.symm b)) N (fun b => r (e.symm b)) := by
  have hcard : Fintype.card (A → ZMod N) = Fintype.card (B → ZMod N) :=
    Fintype.card_congr (outputAxisReindexAddEquiv e (ZMod N)).toEquiv
  have heq (ω : Ω) :
      ((fun b : B => (Y ω (e.symm b) : ZMod N)) = fun b => r (e.symm b)) ↔
        ((fun a : A => (Y ω a : ZMod N)) = r) := by
    constructor
    · intro h
      funext a
      simpa only [Equiv.symm_apply_apply] using congrFun h (e a)
    · intro h
      exact congrArg (fun f : A → ZMod N => fun b => f (e.symm b)) h
  unfold rationalOutputDensity finiteImageMass
  simp only [hcard, heq]

theorem rationalInactiveForecast_axis_reindex {I Ω Z A B : Type*}
    [Fintype I] [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (inactive : FiniteProbabilityWeights I)
    (active : I → FiniteProbabilityWeights Ω) (gridPoint : I → Z)
    (Y : I → Ω → A → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (r : A → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z r =
      rationalInactiveForecast inactive active gridPoint
        (fun i ω b => Y i ω (e.symm b)) N gridVolume z (fun b => r (e.symm b)) := by
  unfold rationalInactiveForecast
  apply congrArg (gridVolume * ·)
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact rationalOutputDensity_axis_reindex e (active i) (Y i) N r

theorem outputAxisCharacterPullback_order {A B : Type*} (e : A ≃ B)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    orderOf (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) =
      orderOf χ :=
  characterPullback_order _ (outputAxisReindexAddEquiv e (ZMod N)).surjective χ

theorem finiteImageCharacteristic_axis_reindex {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ =
      finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N))
        (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) := rfl

theorem finiteImageCharacteristic_axis_reindex_bound {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) {D P : ℝ}
    (hdecay : ∀ χ : AddChar (A → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ : AddChar (B → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P) := by
  intro χ
  rw [finiteImageCharacteristic_axis_reindex]
  simpa only [outputAxisCharacterPullback_order] using
    hdecay (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ)

end Erdos3

end

end OAI
