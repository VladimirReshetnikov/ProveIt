import GRHArticle.ProgressionFree.IntervalRothCertificate
import Mathlib.Data.Nat.Bits

/-!
# Bit-mask certificates for Roth numbers of finite intervals

At position `y` the past mask reads the selected positions backwards from
`y-1`, while the remaining mask reads forwards from `y`. Selecting `y`
therefore forbids precisely the corresponding reflected positions. The
bonus mask assigns an extra unit of weight to specified positions.
-/

namespace GRHArticle.ProgressionFree

private def maskCapacity : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, r, b =>
    if r=0 then 0 else
      (if r.testBit 0 then 1+(b.testBit 0).toNat else 0) + maskCapacity n (r >>> 1) (b >>> 1)

/-- Branch on selecting the leftmost available position, with early
termination whenever the remaining weight cannot exceed the target. -/
def intervalMaskCheckWith (capacity : ℕ → ℕ → ℕ → ℕ) (M : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, spent, _, _, _ => decide (spent ≤ M)
  | n+1, spent, p, r, b =>
    if spent + capacity (n+1) r b ≤ M then true else
      let s := r >>> 1
      let a := b >>> 1
      intervalMaskCheckWith capacity M n spent (2*p) s a &&
        (!r.testBit 0 || intervalMaskCheckWith capacity M n (spent+1+(b.testBit 0).toNat)
          (2*p+1) (s ^^^ (s &&& p)) a)


/-- Use the full remaining weight as a bound, without a separate certificate. -/
def intervalMaskCheck := intervalMaskCheckWith maskCapacity

def intervalChosenMass (B : Finset ℕ) (y n b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if y+j ∈ B then 1+(b.testBit j).toNat else 0

private theorem intervalChosenMass_succ (B : Finset ℕ) (y n b : ℕ) :
    intervalChosenMass B y (n+1) b = (if y ∈ B then 1+(b.testBit 0).toNat else 0) +
      intervalChosenMass B (y+1) n (b >>> 1) := by
  unfold intervalChosenMass
  rw [Finset.sum_range_succ',Nat.add_comm]
  simp only [Nat.add_zero, Nat.testBit_shiftRight]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Nat.add_comm 1 j,Nat.add_right_comm y 1 j,Nat.add_assoc]

def IntervalMaskAvailable (B : Finset ℕ) (y n r : ℕ) : Prop :=
  ∀ j < n, y+j ∈ B → r.testBit j = true

private theorem IntervalMaskAvailable.tail {B : Finset ℕ} {y n r : ℕ} (h : IntervalMaskAvailable B y (n+1) r) :
    IntervalMaskAvailable B (y+1) n (r >>> 1) := by
  intro j hj hm
  rw [Nat.testBit_shiftRight]
  exact h (1+j) (by omega) (Nat.add_assoc y 1 j ▸ hm)

private theorem intervalChosenMass_le_capacity (B : Finset ℕ) (y n r b : ℕ) (hr : IntervalMaskAvailable B y n r) :
    intervalChosenMass B y n b ≤ maskCapacity n r b := by
  induction n generalizing y r b with
  | zero => simp [intervalChosenMass,maskCapacity]
  | succ n ih =>
    rw [intervalChosenMass_succ,maskCapacity]
    by_cases h0 : r = 0
    · subst r
      have he : intervalChosenMass B (y+1) n (b >>> 1) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hf : y+1+j ∉ B := fun hm ↦ by
          have h := hr.tail j (Finset.mem_range.mp hj) hm
          simp at h
        simp [hf]
      have hy : y ∉ B := fun hm ↦ by simpa using hr 0 (by omega) (by simpa using hm)
      simp [hy,he]
    · rw [if_neg h0]
      have ht := ih (y+1) (r >>> 1) (b >>> 1) hr.tail
      by_cases hy : y ∈ B
      · have hb := hr 0 (by omega) (by simpa using hy)
        simp [hy,hb,ht]
      · simp only [if_neg hy,zero_add]
        omega

private def Past (B : Finset ℕ) (y p : ℕ) : Prop :=
  ∀ j, p.testBit j = true → j < y ∧ y-1-j ∈ B

private theorem Past.next {B : Finset ℕ} {y p : ℕ} (h : Past B y p)
    (v : Bool) (hv : v = true → y ∈ B) : Past B (y+1) (Nat.bit v p) := by
  intro j hj
  cases j with
  | zero => simpa using And.intro (Nat.zero_lt_succ y) (hv ((Nat.testBit_bit_zero v p) ▸ hj))
  | succ j =>
    rw [Nat.testBit_bit_succ] at hj
    obtain ⟨hj,hm⟩ := h j hj
    exact ⟨by omega,(show y+1-1-(j+1) = y-1-j by omega) ▸ hm⟩

private theorem intervalMaskCheck_sound_at (B : Finset ℕ) (hf : ThreeAPFree (B : Set ℕ)) (capacity : ℕ → ℕ → ℕ → ℕ)
    (hcap : ∀ y n r b, IntervalMaskAvailable B y n r → intervalChosenMass B y n b ≤ capacity n r b)
    (M n : ℕ) :
    ∀ y spent p r b, Past B y p → IntervalMaskAvailable B y n r →
      intervalMaskCheckWith capacity M n spent p r b = true → spent + intervalChosenMass B y n b ≤ M := by
  induction n with
  | zero => simp [intervalMaskCheckWith,intervalChosenMass]
  | succ n ih =>
    intro y spent p r b hp hr hc
    rw [intervalMaskCheckWith] at hc
    split at hc
    · exact (Nat.add_le_add_left (hcap y _ r b hr) spent).trans (by assumption)
    obtain ⟨hskip,htake⟩ := Bool.and_eq_true_iff.mp hc
    rw [intervalChosenMass_succ]
    by_cases hy : y ∈ B
    · have hr₀ := hr 0 (by omega) (by simpa using hy)
      simp only [hr₀,Bool.not_true,Bool.false_or] at htake
      have hr' : IntervalMaskAvailable B (y+1) n ((r >>> 1) ^^^ ((r >>> 1) &&& p)) := by
        intro j hj hm
        have hb : p.testBit j = false := by
          cases he : p.testBit j with
          | false => rfl
          | true =>
            obtain ⟨hj',hprev⟩ := hp j he
            have hdiff := hf hprev hy hm (by omega)
            omega
        rw [Nat.testBit_xor,Nat.testBit_and,hr.tail j hj hm,hb]
        rfl
      have hprev : Past B (y+1) (2*p+1) := by simpa only [Nat.bit_true] using hp.next true (fun _ ↦ hy)
      have h := ih (y+1) _ _ _ _ hprev hr' htake
      simp only [if_pos hy]
      omega
    · have hprev : Past B (y+1) (2*p) := by simpa only [Nat.bit_false] using hp.next false (by simp)
      simpa only [if_neg hy, zero_add] using ih (y+1) _ _ _ _ hprev hr.tail hskip

/-- A successful interval mask computation bounds the size of every
admissible subset of the input mask, including the extra weight on each
selected bonus position. -/
theorem intervalMaskCheckWith_sound (capacity : ℕ → ℕ → ℕ → ℕ) {n M r b : ℕ}
    (hc : intervalMaskCheckWith capacity M n 0 0 r b = true)
    {B : Finset ℕ} (hf : ThreeAPFree (B : Set ℕ)) (hB : B ⊆ Finset.range n)
    (hr : ∀ j ∈ B, r.testBit j = true)
    (hcap : ∀ y n r b, IntervalMaskAvailable B y n r → intervalChosenMass B y n b ≤ capacity n r b) :
    ∑ j ∈ B, (1+(b.testBit j).toNat) ≤ M := by
  have hp : Past B 0 0 := by intro j hj; simp at hj
  have h := intervalMaskCheck_sound_at B hf capacity hcap M n 0 0 0 r b hp
    (fun j _ hj ↦ hr j (by simpa using hj)) hc
  simp only [Nat.zero_add,intervalChosenMass,← Finset.sum_filter] at h
  have he : (Finset.range n).filter (· ∈ B) = B := by
    ext j; simp only [Finset.mem_filter]; exact ⟨And.right,fun hj ↦ ⟨hB hj,hj⟩⟩
  rwa [he] at h

theorem intervalMaskCheck_sound {n M r b : ℕ} (hc : intervalMaskCheck M n 0 0 r b = true)
    {B : Finset ℕ} (hf : ThreeAPFree (B : Set ℕ)) (hB : B ⊆ Finset.range n)
    (hr : ∀ j ∈ B, r.testBit j = true) :
    ∑ j ∈ B, (1+(b.testBit j).toNat) ≤ M :=
  intervalMaskCheckWith_sound maskCapacity hc hf hB hr (intervalChosenMass_le_capacity B)

end GRHArticle.ProgressionFree
