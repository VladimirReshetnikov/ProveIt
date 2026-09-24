import Diophantine.Paper1980.Compile93a
import Diophantine.Paper1980.Csq90

/-!
# Row shapes of the 90-operation compiler

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 2.  The compiled circuit uses
the quadratic row shapes of the 93-operation compiler (`Compile93a.lean`:
`copyRow`, `addRow`, `mulRow`, `zeroRow`, `oneRow`, `deltaRow`, `unitRow`),
together with

* the seed row `seedRow = −x²`;
* the reverse row `revRow δ V = 2 x δ − 2 δ ΣV`;
* the normalization row `uRow90 V X δ δ' u = 2 ΣV ΣX − 2 δ δ' − 2 δ Σu`,

so that every ordinary row is free of the input `x`.  Structural validity
(`Iso.RowStruct`) together with the sign conditions and the disjointness of
the helper group from the row's coordinates gives the validity `RowOk` of the
90-operation layout (`rowOk_of_struct`).
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Iso (negRow S sqTerms crossTerms prodTerms dotTerms copyRow normRow addRow mulRow zeroRow
  oneRow deltaRow uRow unitRow RowStruct Disj Avoids)

variable {m : ℕ}

/-! ### The new shapes -/

/-- The seed row `−x²`. -/
def seedRow : Row m := ⟨[], [], [], -1⟩

/-- The reverse row `2 x δ − 2 δ Σg`. -/
def revRow (d : Fin m) (g : Fin 3 → Fin m) : Row m := ⟨[], dotTerms g d (-1), [(d, 1)], 0⟩

/-- The normalization row `2 Σg Σh − 2 δ δ' − 2 δ Σu`. -/
def uRow90 (g h : Fin 3 → Fin m) (d d' : Fin m) (u : Fin 3 → Fin m) : Row m :=
  ⟨[], prodTerms g h 1 ++ [(d, d', -1)] ++ dotTerms u d (-1), [], 0⟩

variable (x : ℤ) (z : Fin m → ℤ)

theorem seedRow_val : (seedRow : Row m).val x z = -x ^ 2 := by
  simp [seedRow, Row.val]

theorem revRow_val (d : Fin m) (g : Fin 3 → Fin m) :
    (revRow d g).val x z = 2 * x * z d - 2 * z d * S g z := by
  simp [revRow, dotTerms, Row.val, S]; ring

theorem uRow90_val (g h : Fin 3 → Fin m) (d d' : Fin m) (u : Fin 3 → Fin m) :
    (uRow90 g h d d' u).val x z = 2 * S g z * S h z - 2 * z d * z d' - 2 * z d * S u z := by
  simp [uRow90, prodTerms, dotTerms, Row.val, S]; ring

/-! ### Structural validity of the new shapes -/

theorem seedRow_struct : RowStruct (seedRow : Row m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [seedRow]

theorem revRow_struct {d : Fin m} {g : Fin 3 → Fin m} (hg : Function.Injective g)
    (hgd : Avoids g d) : RowStruct (revRow d g) := by
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [revRow, dotTerms, hg.eq_iff, hgd _, hdg]

theorem uRow90_struct {g h u : Fin 3 → Fin m} {d d' : Fin m} (hg : Function.Injective g)
    (hh : Function.Injective h) (hu : Function.Injective u) (hgh : Disj g h) (hgu : Disj g u)
    (hhu : Disj h u) (hgd : Avoids g d) (hgd' : Avoids g d') (hhd : Avoids h d)
    (hhd' : Avoids h d') (hud : Avoids u d) (hud' : Avoids u d') (hdd : d ≠ d') :
    RowStruct (uRow90 g h d d' u) := by
  have hhg := hgh.symm; have hug := hgu.symm; have huh := hhu.symm
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  have hd'g : ∀ a, d' ≠ g a := fun a => (hgd' a).symm
  have hdh : ∀ a, d ≠ h a := fun a => (hhd a).symm
  have hd'h : ∀ a, d' ≠ h a := fun a => (hhd' a).symm
  have hdu : ∀ a, d ≠ u a := fun a => (hud a).symm
  have hd'u : ∀ a, d' ≠ u a := fun a => (hud' a).symm
  have hd'd : d' ≠ d := hdd.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [uRow90, prodTerms, dotTerms, hg.eq_iff, hh.eq_iff, hu.eq_iff, hgh _ _, hhg _ _,
      hgu _ _, hug _ _, hhu _ _, huh _ _, hgd _, hgd' _, hhd _, hhd' _, hud _, hud' _, hdg, hd'g,
      hdh, hd'h, hdu, hd'u, hdd, hd'd]

/-! ### From structural validity to `RowOk` -/

/-- The multiset keys of a structurally valid row are distinct. -/
theorem terms_nodup_of_struct {R : Row m} (hS : RowStruct R) : ((terms R).map Prod.fst).Nodup := by
  unfold terms
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def]
  have hA : (R.sq.map fun p => ({p.1, p.1} : Multiset (Fin m))).Nodup := by
    have e : (R.sq.map fun p => ({p.1, p.1} : Multiset (Fin m))) =
        (R.sq.map Prod.fst).map (fun i : Fin m => ({i, i} : Multiset (Fin m))) := by
      rw [List.map_map]; rfl
    rw [e]
    exact hS.sq_nodup.map (fun i k (hik : ({i, i} : Multiset (Fin m)) = {k, k}) => by
      rcases pair_eq hik with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1)
  have hB : (R.cross.map fun q => ({q.1, q.2.1} : Multiset (Fin m))).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hS.cross_pw.imp ?_
    intro p q ⟨h1, h2⟩ heq
    rcases pair_eq heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact h1 ⟨e1, e2⟩
    · exact h2 ⟨e1, e2⟩
  have hC : (R.xz.map fun p => ({p.1} : Multiset (Fin m))).Nodup := by
    have e : (R.xz.map fun p => ({p.1} : Multiset (Fin m))) =
        (R.xz.map Prod.fst).map (fun i : Fin m => ({i} : Multiset (Fin m))) := by
      rw [List.map_map]; rfl
    rw [e]
    exact hS.xz_nodup.map (fun i k hik => Multiset.singleton_inj.1 hik)
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨hA, hB, ?_⟩, hC, ?_⟩, List.nodup_singleton 0, ?_⟩
  · -- squares versus cross terms
    intro a ha b hb
    rw [List.mem_map] at ha hb
    obtain ⟨p, _, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    intro heq
    rcases pair_eq heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hS.cross_ne q hq (e1.symm.trans e2)
    · exact hS.cross_ne q hq (e2.symm.trans e1)
  · -- squares and cross terms versus `xz` terms
    intro a ha b hb
    rw [List.mem_append] at ha
    rw [List.mem_map] at hb
    obtain ⟨r, _, rfl⟩ := hb
    rcases ha with ha | ha <;> rw [List.mem_map] at ha <;> obtain ⟨p, _, rfl⟩ := ha <;>
      intro heq <;> have := congrArg Multiset.card heq <;> simp at this
  · -- everything versus the constant term
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    simp only [List.mem_append, List.mem_map] at ha
    rcases ha with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩ <;>
      intro heq <;> have := congrArg Multiset.card heq <;> simp at this

/-- Structural validity, the sign conditions, the disjointness of the helper group from the
row's coordinates, and the seed condition give `RowOk`. -/
theorem rowOk_of_struct {R : Row m} {P : Fin 3 → Fin m} (hS : RowStruct R)
    (hxz : ∀ q ∈ R.xz, 0 ≤ q.2) (hxx : R.xx ≤ 0) (hP : Function.Injective P)
    (hsq : ∀ q ∈ R.sq, ∀ a, P a ≠ q.1) (hcr : ∀ q ∈ R.cross, ∀ a, P a ≠ q.1 ∧ P a ≠ q.2.1)
    (hseed : R.xx < 0 → R.sq = [] ∧ R.cross = [] ∧ R.xz = []) : RowOk R P where
  coeff := by
    intro p hp
    unfold terms at hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | rfl
    · exact hS.sq_sign q hq
    · exact hS.cross_sign q hq
    · exact hS.xz_sign q hq
    · exact hS.xx_sign
  nodup := terms_nodup_of_struct hS
  cross := hS.cross_ne
  xz := hxz
  xx := hxx
  disj := by
    intro μ hμ a
    obtain ⟨c, hc, hneg⟩ := (mem_negs).1 hμ
    unfold terms at hc
    simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ((⟨q, hq, h1, _⟩ | ⟨q, hq, h1, _⟩) | ⟨q, hq, h1, h2⟩) | ⟨h1, _⟩
    · rw [← h1]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
      exact ⟨hsq q hq a, hsq q hq a⟩
    · rw [← h1]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
      exact hcr q hq a
    · exfalso; have := hxz q hq; omega
    · rw [h1]; exact Multiset.notMem_zero _
  inj := hP
  seed := hseed

end L90

end Jones1980
