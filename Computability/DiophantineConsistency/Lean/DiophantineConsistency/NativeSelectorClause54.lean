import DiophantineConsistency.NativeLocalCoefficients54
import Mathlib.Algebra.BigOperators.ModEq

/-! # The exact compact54 clause for arbitrary Boolean selector assignments -/

namespace DiophantineConsistency.NativeSelectorClause54

open NativeClause54 NativeClauseModes54 NativeModesData54 NativeLocalCoefficients54
open scoped BigOperators

def selectorCount (x : Fin 457 → ℕ) : ℕ := ∑ i, x i

def selectorWord (x : Fin 457 → ℕ) : ℕ :=
  ∑ i, x i * selectorCoefficient (mode i).2 (mode i).1

def nativeWord (x : Fin 457 → ℕ) (QR QL u Z y A1 A2 : ℕ) : ℕ :=
  selectorWord x + auxiliaryWord QR QL u + copiedWord Z y A1 A2

theorem selectorCount_le (x : Fin 457 → ℕ) (hx : ∀ i, x i ≤ 1) : selectorCount x ≤ 457 := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 457))) (fun i _ => hx i)
  simpa only [selectorCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,mul_one] using hs

theorem nativeWord_mod (x : Fin 457 → ℕ) (QR QL u Z y A1 A2 : ℕ) :
    nativeWord x QR QL u Z y A1 A2 ≡ selectorCount x [MOD 512] := by
  have hc (i : Fin 457) : selectorCoefficient (mode i).2 (mode i).1 ≡ 1 [MOD 512] := by
    change selectorCoefficient (mode i).2 (mode i).1 % 512 = 1
    unfold selectorCoefficient
    omega
  have hs : selectorWord x ≡ selectorCount x [MOD 512] := by
    apply Nat.ModEq.sum
    intro i _
    simpa only [mul_one] using (hc i).mul_left (x i)
  have ha : auxiliaryWord QR QL u ≡ 0 [MOD 512] := by
    change auxiliaryWord QR QL u % 512 = 0
    unfold auxiliaryWord
    omega
  have hz : copiedWord Z y A1 A2 ≡ 0 [MOD 512] := by
    change copiedWord Z y A1 A2 % 512 = 0
    unfold copiedWord
    omega
  simpa only [nativeWord,add_zero] using (hs.add ha).add hz

/-- The complete selector count is recovered from the actual coefficient
sum, before imposing any one-hot assumption. -/
theorem selectorCount_le_one (x : Fin 457 → ℕ) (hx : ∀ i, x i ≤ 1)
    {QR QL u Z y A1 A2 : ℕ}
    (hmask : nativeWord x QR QL u Z y A1 A2 &&& clauseMask = 0) : selectorCount x ≤ 1 := by
  have hc : selectorCount x < 512 := by have := selectorCount_le x hx; omega
  have hb := congrArg (fun z : ℕ => z % 2 ^ 9) hmask
  rw [Nat.and_mod_two_pow] at hb
  have hmu : clauseMask % 512 = 510 := by decide
  have hw : nativeWord x QR QL u Z y A1 A2 % 512 = selectorCount x % 512 :=
    nativeWord_mod x QR QL u Z y A1 A2
  change nativeWord x QR QL u Z y A1 A2 % 512 &&& clauseMask % 512 = 0 at hb
  rw [hmu,hw,Nat.mod_eq_of_lt hc] at hb
  exact (selector_iff hc).mp hb

theorem selectors_zero (x : Fin 457 → ℕ) (h : selectorCount x = 0) : ∀ i, x i = 0 := by
  intro i
  have hi : x i ≤ ∑ j : Fin 457, x j := Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i)
  change x i ≤ selectorCount x at hi
  omega

theorem selectors_one (x : Fin 457 → ℕ) (h : selectorCount x = 1) :
    ∃ i, x i = 1 ∧ ∀ j, j ≠ i → x j = 0 := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra he
    push Not at he
    have hz : selectorCount x = 0 := by simp [selectorCount,he]
    omega
  obtain ⟨i,hi⟩ := hex
  have hs := Finset.sum_le_one_iff.mp (show (∑ j : Fin 457, x j) ≤ 1 by exact h.le)
  have hii : x i = 1 := (hs i i (Finset.mem_univ i) (Finset.mem_univ i) hi hi).2
  refine ⟨i,hii,?_⟩
  intro j hji
  by_contra hj
  exact hji (hs j i (Finset.mem_univ j) (Finset.mem_univ i) hj hi).1

theorem nativeWord_single (i : Fin 457) (x : Fin 457 → ℕ) (n QR QL u Z y A1 A2 : ℕ)
    (hx : ∀ j, x j = if j = i then n else 0) :
    nativeWord x QR QL u Z y A1 A2 = localClause (mode i).2 (mode i).1 n QR QL u Z y A1 A2 := by
  have hxF : x = (fun j => if j = i then n else 0) := funext hx
  have hs : selectorWord x = n * selectorCoefficient (mode i).2 (mode i).1 := by
    simp [selectorWord,hxF,ite_mul]
  unfold nativeWord
  rw [hs]
  exact coefficient_word_eq _ _ _ _ _ _ _ _ _ _

def Empty (x : Fin 457 → ℕ) (QR QL u Z y A1 A2 : ℕ) : Prop :=
  (∀ i, x i = 0) ∧ QR = 0 ∧ QL = 0 ∧ u = 0 ∧ Z = 0 ∧ y = 0 ∧ A1 = 0 ∧ A2 = 0

def Occupied (x : Fin 457 → ℕ) (QR QL u Z y A1 A2 : ℕ) : Prop :=
  ∃ i, x i = 1 ∧ (∀ j, j ≠ i → x j = 0) ∧ Allowed (mode i).2 QR QL u ∧
    y = 1 ∧ A1 = 1 ∧ A2 = 1 ∧ encode (expanded (mode i).1 QR QL u) + Z = labelBase - 1

/-- The actual457 selector coefficient sum accepts exactly an empty cell
or one correctly expanded and complemented tile. -/
theorem native_clause_iff (x : Fin 457 → ℕ) (hx : ∀ i, x i ≤ 1)
    {QR QL u Z y A1 A2 : ℕ} (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1)
    (hZ : Z < labelBase) (hZbit : Z % 2 = y) (hy : y ≤ 1) (hA1 : A1 ≤ 1) (hA2 : A2 ≤ 1) :
    nativeWord x QR QL u Z y A1 A2 &&& clauseMask = 0 ↔
      Empty x QR QL u Z y A1 A2 ∨ Occupied x QR QL u Z y A1 A2 := by
  constructor
  · intro hmask
    have hc := selectorCount_le_one x hx hmask
    by_cases hc0 : selectorCount x = 0
    · have hx0 := selectors_zero x hc0
      have heq := nativeWord_single 0 x 0 QR QL u Z y A1 A2 (by intro j; simp [hx0 j])
      rw [heq] at hmask
      obtain he | ho := (local_clause_iff (mode_valid 0) (by decide : 0 < 512)
        hQR hQL hu hZ hZbit hy hA1 hA2).mp hmask
      · exact Or.inl ⟨hx0,he.2⟩
      · have := ho.1; omega
    · have hc1 : selectorCount x = 1 := by omega
      obtain ⟨i,hi,hother⟩ := selectors_one x hc1
      have heq := nativeWord_single i x 1 QR QL u Z y A1 A2 (by
        intro j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji,hother j hji])
      rw [heq] at hmask
      obtain he | ho := (local_clause_iff (mode_valid i) (by decide : 1 < 512)
        hQR hQL hu hZ hZbit hy hA1 hA2).mp hmask
      · have := he.1; omega
      · exact Or.inr ⟨i,hi,hother,ho.2⟩
  · rintro (⟨hx0,hQR0,hQL0,hu0,hZ0,hy0,hA10,hA20⟩ | ⟨i,hi,hother,ha,hy1,hA11,hA21,hcomp⟩)
    · have heq := nativeWord_single 0 x 0 QR QL u Z y A1 A2 (by intro j; simp [hx0 j])
      rw [heq]
      exact (local_clause_iff (mode_valid 0) (by decide : 0 < 512) hQR hQL hu hZ hZbit hy hA1 hA2).mpr
        (Or.inl ⟨rfl,hQR0,hQL0,hu0,hZ0,hy0,hA10,hA20⟩)
    · have heq := nativeWord_single i x 1 QR QL u Z y A1 A2 (by
        intro j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji,hother j hji])
      rw [heq]
      exact (local_clause_iff (mode_valid i) (by decide : 1 < 512) hQR hQL hu hZ hZbit hy hA1 hA2).mpr
        (Or.inr ⟨rfl,ha,hy1,hA11,hA21,hcomp⟩)

/-- Both standalone anchors and the copied west parity bit equal the
occupation bit. This is the local input to global phase synchronization. -/
theorem anchors_eq_selectorCount (x : Fin 457 → ℕ) (hx : ∀ i, x i ≤ 1)
    {QR QL u Z y A1 A2 : ℕ} (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1)
    (hZ : Z < labelBase) (hZbit : Z % 2 = y) (hy : y ≤ 1) (hA1 : A1 ≤ 1) (hA2 : A2 ≤ 1)
    (hmask : nativeWord x QR QL u Z y A1 A2 &&& clauseMask = 0) :
    y = selectorCount x ∧ A1 = selectorCount x ∧ A2 = selectorCount x := by
  obtain he | ho := (native_clause_iff x hx hQR hQL hu hZ hZbit hy hA1 hA2).mp hmask
  · obtain ⟨hx0,_,_,_,_,hy0,hA10,hA20⟩ := he
    have hc : selectorCount x = 0 := by simp [selectorCount,hx0]
    exact ⟨hy0.trans hc.symm,hA10.trans hc.symm,hA20.trans hc.symm⟩
  · obtain ⟨i,hi,hother,_,hy1,hA11,hA21,_⟩ := ho
    have hxF : x = (fun j => if j = i then 1 else 0) := by
      funext j
      by_cases hji : j = i
      · subst j; simp [hi]
      · simp [hji,hother j hji]
    have hc : selectorCount x = 1 := by simp [selectorCount,hxF]
    exact ⟨hy1.trans hc.symm,hA11.trans hc.symm,hA21.trans hc.symm⟩

end DiophantineConsistency.NativeSelectorClause54
