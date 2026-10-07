import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import OAI.Combinatorics.Progressions.Dynamics.ModularDecayBudget
import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
import OAI.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling

namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, AddCommGroup (H j)]

def finiteProductCharacter : (∀ j, AddChar (H j) ℂ) →* AddChar (∀ j, H j) ℂ where
  toFun χ := {
    toFun := fun y => ∏ j, χ j (y j)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by intro x y; simp only [Pi.add_apply, AddChar.map_add_eq_mul,
      Finset.prod_mul_distrib] }
  map_one' := by ext y; simp
  map_mul' χ ψ := by ext y; simp [Finset.prod_mul_distrib]

def finiteProductCharacterCoordinate (χ : AddChar (∀ j, H j) ℂ) (j : J) :
    AddChar (H j) ℂ where
  toFun x := χ (Pi.single j x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [Pi.single_add, χ.map_add_eq_mul]

theorem finiteProductCharacter_single (χ : ∀ j, AddChar (H j) ℂ) (j : J) (x : H j) :
    finiteProductCharacter χ (Pi.single j x) = χ j x := by
  change (∏ i, χ i (Pi.single j x i)) = _
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, AddChar.map_zero_eq_one]
  · simp

theorem finiteProductCharacter_injective : Function.Injective
    (finiteProductCharacter (H := H)) := by
  intro χ ψ h
  funext j
  apply AddChar.ext
  intro x
  have := congrArg (fun θ : AddChar (∀ j, H j) ℂ => θ (Pi.single j x)) h
  simpa only [finiteProductCharacter_single] using this

theorem finiteProductCharacter_decomposition (χ : AddChar (∀ j, H j) ℂ) :
    finiteProductCharacter (finiteProductCharacterCoordinate χ) = χ := by
  ext x
  change (∏ j, χ (Pi.single j (x j))) = χ x
  have hsum : (∑ j, Pi.single j (x j)) = x := by
    ext i
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
  have h := map_sum χ.toAddMonoidHom (fun j => Pi.single j (x j)) Finset.univ
  change χ (∑ j, Pi.single j (x j)) = ∏ j, χ (Pi.single j (x j)) at h
  exact (hsum ▸ h).symm

theorem finiteProductCharacter_order (χ : ∀ j, AddChar (H j) ℂ)
    (hcop : Pairwise (fun i j => Nat.Coprime (orderOf (χ i)) (orderOf (χ j)))) :
    orderOf (finiteProductCharacter χ) = ∏ j, orderOf (χ j) := by
  rw [orderOf_injective finiteProductCharacter finiteProductCharacter_injective χ,
    Pi.orderOf]
  exact Finset.lcm_eq_prod (fun i _ j _ hij => hcop hij)

variable [∀ j, Fintype (H j)] {X : J → Type*} [∀ j, Fintype (X j)]

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_product (p : ∀ j, FiniteProbabilityWeights (X j))
    (Y : ∀ j, X j → H j) (χ : ∀ j, AddChar (H j) ℂ) :
    finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x j => Y j (x j)) (finiteProductCharacter χ) =
      ∏ j, finiteImageCharacteristic (p j) (Y j) (χ j) :=
  FiniteProbabilityWeights.complexMean_pi_product p (fun j x => χ j (Y j x))

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_product_decay
    (p : ∀ j, FiniteProbabilityWeights (X j)) (Y : ∀ j, X j → H j)
    (χ : ∀ j, AddChar (H j) ℂ) (c : J → ℝ) (P₁ P : ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hcop : Pairwise (fun i j => Nat.Coprime (orderOf (χ i)) (orderOf (χ j))))
    (hdecay : ∀ j, ‖finiteImageCharacteristic (p j) (Y j) (χ j)‖ ≤
      c j ^ P₁ * (orderOf (χ j) : ℝ) ^ (-P)) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x j => Y j (x j)) (finiteProductCharacter χ)‖ ≤
      (∏ j, c j) ^ P₁ * (orderOf (finiteProductCharacter χ) : ℝ) ^ (-P) := by
  rw [finiteImageCharacteristic_product, finiteProductCharacter_order χ hcop,
    Nat.cast_prod]
  exact modular_product_decay_budget Finset.univ c (fun j => orderOf (χ j))
    (fun j => finiteImageCharacteristic (p j) (Y j) (χ j)) P₁ P
    (fun j _ => hc j) (fun j _ => Nat.cast_nonneg _) (fun j _ => hdecay j)

omit [Fintype J] [∀ j, Fintype (H j)] in

theorem finiteProductCharacterCoordinate_order_dvd
    (χ : AddChar (∀ j, H j) ℂ) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0) (j : J) :
    orderOf (finiteProductCharacterCoordinate χ j) ∣ q j := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hkill, AddChar.map_zero_eq_one,
    AddChar.one_apply]

omit [Fintype J] [∀ j, Fintype (H j)] in

theorem finiteProductCharacterCoordinate_coprime
    (χ : AddChar (∀ j, H j) ℂ) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0)
    (hq : Pairwise (fun i j => Nat.Coprime (q i) (q j))) :
    Pairwise (fun i j => Nat.Coprime (orderOf (finiteProductCharacterCoordinate χ i))
      (orderOf (finiteProductCharacterCoordinate χ j))) := by
  intro i j hij
  exact (hq hij).of_dvd (finiteProductCharacterCoordinate_order_dvd χ q hkill i)
    (finiteProductCharacterCoordinate_order_dvd χ q hkill j)

omit [∀ j, Fintype (H j)] in

theorem finiteImageCharacteristic_crt_decay {G : Type*} [AddCommGroup G] [Fintype G]
    (e : G ≃+ (∀ j, H j)) (p : ∀ j, FiniteProbabilityWeights (X j))
    (Y : ∀ j, X j → H j) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0)
    (hq : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (c : J → ℝ) (P₁ P : ℝ) (hc : ∀ j, 0 ≤ c j)
    (hdecay : ∀ j (ψ : AddChar (H j) ℂ),
      ‖finiteImageCharacteristic (p j) (Y j) ψ‖ ≤ c j ^ P₁ * (orderOf ψ : ℝ) ^ (-P))
    (χ : AddChar G ℂ) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.pi p)
      (fun x => e.symm (fun j => Y j (x j))) χ‖ ≤
      (∏ j, c j) ^ P₁ * (orderOf χ : ℝ) ^ (-P) := by
  let ψ := characterPullback e.symm.toAddMonoidHom χ
  have hord : orderOf ψ = orderOf χ :=
    characterPullback_order e.symm.toAddMonoidHom e.symm.surjective χ
  have h := finiteImageCharacteristic_product_decay p Y
    (finiteProductCharacterCoordinate ψ) c P₁ P hc
    (finiteProductCharacterCoordinate_coprime ψ q hkill hq)
    (fun j => hdecay j _)
  rw [finiteProductCharacter_decomposition, hord] at h
  exact h

end Erdos3

end

end OAI
