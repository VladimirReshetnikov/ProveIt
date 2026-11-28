import GRHArticle.ProgressionFree.PolynomialOneFreePrimeFibers

/-!
# Adjoining allowed powers of one prime to a monic family

Unique factorization makes the target degree layer a disjoint union of
lower-degree layers, one for each allowed prime exponent. No restriction
on the degree of the prime or the exponent set is needed.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- Extend a family by the prescribed powers of a fixed polynomial. -/
def extendByPrimePowers (P : F[X]) (D : Set ℕ) (B : Set F[X]) : Set F[X] :=
  {f | ∃ g ∈ B, ∃ e ∈ D, f = g * P^e}

/-- Monic polynomials of degree `n` in a given family. -/
noncomputable def monicFamilyLayer [Fintype F] (B : Set F[X]) (n : ℕ) : Finset F[X] :=
  (monicLayer F n).filter (· ∈ B)

theorem mem_monicFamilyLayer [Fintype F] {B : Set F[X]} {n : ℕ} {f : F[X]} :
    f ∈ monicFamilyLayer B n ↔ f.Monic ∧ f.natDegree = n ∧ f ∈ B := by
  simp [monicFamilyLayer, mem_monicLayer, and_assoc]

theorem card_monicFamilyLayer_le [Fintype F] (B : Set F[X]) (n : ℕ) :
    (monicFamilyLayer B n).card ≤ Fintype.card F ^ n := by
  rw [← card_monicLayer (F := F)]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Read back a monic cofactor and the prescribed prime exponent. -/
theorem primePowerRepresentation_injective {P g h : F[X]} {e j : ℕ} (hP : P.Monic)
    (hi : Irreducible P) (hg : g.Monic) (hh : h.Monic) (hpg : ¬P ∣ g) (hph : ¬P ∣ h)
    (he : g*P^e = h*P^j) : e = j ∧ g = h := by
  have h₁ := congrArg (polynomialPrimeExponent P) he
  have get (a : F[X]) (hm : a.Monic) (hn : ¬P ∣ a) (n : ℕ) :
      polynomialPrimeExponent P (a*P^n) = n := by
    simpa using polynomialPrimeExponent_scalar_mul_cofactor_mul_pow hP hi hm hn
      (one_ne_zero (α := F)) n
  rw [get _ hg hpg, get _ hh hph] at h₁
  subst j
  exact ⟨rfl, mul_right_cancel₀ (pow_ne_zero _ hi.ne_zero) he⟩

/-- Exact count after adjoining powers of any monic irreducible. -/
theorem card_monicFamilyLayer_extendByPrimePowers [Fintype F] {P : F[X]}
    (hP : P.Monic) (hi : Irreducible P) (D : Set ℕ) {B : Set F[X]}
    (hB : ∀ g ∈ B, g.Monic ∧ ¬P ∣ g) (n : ℕ) :
    (monicFamilyLayer (extendByPrimePowers P D B) n).card =
      ∑ e ∈ (Finset.range (n+1)).filter (fun e ↦ e ∈ D ∧ e*P.natDegree ≤ n),
        (monicFamilyLayer B (n-e*P.natDegree)).card := by
  let E := (Finset.range (n+1)).filter (fun e ↦ e ∈ D ∧ e*P.natDegree ≤ n)
  let T := E.sigma fun e ↦ monicFamilyLayer B (n-e*P.natDegree)
  have hdeg {g : F[X]} (hg : g.Monic) (e : ℕ) :
      (g*P^e).natDegree = g.natDegree + e*P.natDegree := by
    rw [natDegree_mul hg.ne_zero (pow_ne_zero _ hi.ne_zero), natDegree_pow]
  have hcard : T.card = (monicFamilyLayer (extendByPrimePowers P D B) n).card := by
    apply Finset.card_bij (fun a _ ↦ a.2 * P^a.1)
    · rintro ⟨e,g⟩ h
      obtain ⟨he,hg⟩ := Finset.mem_sigma.mp h
      obtain ⟨_,heD,hen⟩ := Finset.mem_filter.mp he
      obtain ⟨hm,hd,hmem⟩ := mem_monicFamilyLayer.mp hg
      exact mem_monicFamilyLayer.mpr ⟨hm.mul (hP.pow e), by rw [hdeg hm, hd]; omega,
        g, hmem, e, heD, rfl⟩
    · rintro ⟨e,g⟩ h ⟨j,k⟩ h' he
      have hg := mem_monicFamilyLayer.mp (Finset.mem_sigma.mp h).2
      have hk := mem_monicFamilyLayer.mp (Finset.mem_sigma.mp h').2
      obtain ⟨rfl,rfl⟩ := primePowerRepresentation_injective hP hi hg.1 hk.1
        (hB _ hg.2.2).2 (hB _ hk.2.2).2 he
      rfl
    · intro f hf
      obtain ⟨_,hd,g,hg,e,he,rfl⟩ := mem_monicFamilyLayer.mp hf
      have hm := (hB g hg).1
      rw [hdeg hm] at hd
      have hen : e*P.natDegree ≤ n := by omega
      have he' : e ≤ e*P.natDegree := Nat.le_mul_of_pos_right e hi.natDegree_pos
      exact ⟨⟨e,g⟩, Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (show e < n+1 by omega), he, hen⟩,
        mem_monicFamilyLayer.mpr ⟨hm, (show g.natDegree = n-e*P.natDegree by omega), hg⟩⟩, rfl⟩
  rw [← hcard, Finset.card_sigma]

end GRHArticle.ProgressionFree
