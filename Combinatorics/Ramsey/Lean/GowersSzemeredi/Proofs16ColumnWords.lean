import GowersSzemeredi.Proofs16FibreGluingCount

/-! Tuples of triples, with alternating signs between successive blocks.
The first endpoint fibre has the sharp dimension bound for every length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A word of `k` triples has exactly `3*k` entries. -/
def ColumnWord (N : Nat) : Nat → Type
  | 0 => Unit
  | k+1 => (ZMod N × ZMod N × ZMod N) × ColumnWord N k

instance columnWordFintype (N : Nat) [NeZero N] : (k : Nat) → Fintype (ColumnWord N k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => letI := columnWordFintype N k;
      inferInstanceAs (Fintype ((ZMod N × ZMod N × ZMod N) × ColumnWord N k))

def columnWordEval {N : Nat} (f : ZMod N → ZMod N) : {k : Nat} → ColumnWord N k → ZMod N
  | 0, _ => 0
  | _+1, w => f w.1.1-f w.1.2.1+f w.1.2.2-columnWordEval f w.2

def columnWordValue {N k : Nat} (w : ColumnWord N k) : ZMod N := columnWordEval id w

def columnWordIn {N : Nat} (B : Finset (ZMod N)) : {k : Nat} → ColumnWord N k → Prop
  | 0, _ => True
  | _+1, w => w.1.1 ∈ B ∧ w.1.2.1 ∈ B ∧ w.1.2.2 ∈ B ∧ columnWordIn B w.2

/-- There are `N^(3*k)` unconstrained words. -/
theorem columnWord_card (N : Nat) [NeZero N] (k : Nat) :
    Fintype.card (ColumnWord N k) = N^(3*k) := by
  induction k with
  | zero => simp [ColumnWord]
  | succ k ih =>
    change Fintype.card ((ZMod N × ZMod N × ZMod N) × ColumnWord N k) = _
    simp only [Fintype.card_prod, ZMod.card, ih]
    rw [Nat.mul_succ, pow_add]
    ring

/-- Fixing the first entry and the value leaves only `3*k+1` free entries
in a word of `k+1` triples. -/
theorem columnWord_first_fibre_card_le {N k : Nat} [NeZero N]
    (S : Finset (ColumnWord N (k+1))) (a x : ZMod N)
    (hS : ∀ w ∈ S, columnWordValue w = a) :
    (S.filter (fun w => w.1.1 = x)).card ≤ N^(3*k+1) := by
  have h := Finset.card_le_card_of_injOn
    (s := S.filter (fun w => w.1.1 = x))
    (t := (Finset.univ : Finset (ZMod N × ColumnWord N k)))
    (fun w => (w.1.2.2,w.2)) (by simp) (by
      intro p hp q hq he
      have hf := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      have hl := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      have hvp := hS p (Finset.mem_filter.mp hp).1
      have hvq := hS q (Finset.mem_filter.mp hq).1
      have hm : p.1.2.1 = q.1.2.1 := by
        change p.1.1-p.1.2.1+p.1.2.2-columnWordValue p.2 = a at hvp
        change q.1.1-q.1.2.1+q.1.2.2-columnWordValue q.2 = a at hvq
        rw [ht] at hvp
        linear_combination -hvp+hvq+hf+hl
      exact Prod.ext (Prod.ext hf (Prod.ext hm hl)) ht)
  simpa [columnWord_card, pow_succ, mul_comm] using h

/-- A dense fixed-value word family has many popular first endpoints. -/
theorem columnWord_popular_first {N k : Nat} [NeZero N]
    (S : Finset (ColumnWord N (k+1))) (B : Finset (ZMod N)) (a : ZMod N)
    {delta : Real} (hd : 0 < delta)
    (hval : ∀ w ∈ S, columnWordValue w = a)
    (hB : ∀ w ∈ S, w.1.1 ∈ B)
    (hmass : delta*(N : Real)^(3*k+2) ≤ S.card) :
    let V := popularEndpointFibres S (fun w => w.1.1) (delta*(N : Real)^(3*k+1)/2)
    V ⊆ B ∧ delta*N/2 ≤ (V.card : Real) := by
  dsimp only
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (popular_endpoint_mem_image _ _ (by positivity) hx)
    exact hB w hw
  · have hc : ∀ x, ((S.filter (fun w => w.1.1 = x)).card : Real) ≤ (N : Real)^(3*k+1) := by
      intro x
      exact_mod_cast columnWord_first_fibre_card_le S a x hval
    have hm : delta*Fintype.card (ZMod N)*(N : Real)^(3*k+1) ≤ S.card := by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmass
    simpa using popular_endpoint_fibres_dense S (fun w => w.1.1) (by positivity) hd.le hc hm

end LeanProofs.GowersSzemeredi
