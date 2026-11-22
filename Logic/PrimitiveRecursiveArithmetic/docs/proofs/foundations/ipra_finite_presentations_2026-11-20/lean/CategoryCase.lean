import Std

/-!
A semantic Lean 4 blueprint for the local image criterion in an inverse tower.
No imports from mathlib or ProveIt. `proj` is the composite of the bonding
maps, supplied with the laws satisfied by the downward loop in the paper.
The source supplies proof terms for the bounded search, certified image lift,
and coherent recursion. See category.tex for the remaining object-language
translation and for the sheafification construction.
-/
namespace IPRAReport.CategoryCase

/-- Test indices below a given bound. The greatest successful index is used. -/
def scan (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n+1 => if p n = true then some n else scan p n

theorem scan_sound (p : Nat → Bool) (n j : Nat) :
    scan p n = some j → j < n ∧ p j = true := by
  induction n with
  | zero => intro h; cases h
  | succ n ih =>
    intro h
    by_cases hp : p n = true
    · have he : n = j := by
        rw [scan, if_pos hp] at h
        exact Option.some.inj h
      subst j
      exact ⟨Nat.lt_succ_self _, hp⟩
    · rw [scan, if_neg hp] at h
      obtain ⟨hlt, hj⟩ := ih h
      exact ⟨Nat.lt_trans hlt (Nat.lt_succ_self _), hj⟩

theorem scan_complete (p : Nat → Bool) (n : Nat) :
    (∃ j, j < n ∧ p j = true) → ∃ j, scan p n = some j := by
  induction n with
  | zero =>
    rintro ⟨j, hj, _⟩
    exact (Nat.not_lt_zero _ hj).elim
  | succ n ih =>
    rintro ⟨j, hj, hp⟩
    by_cases hb : p n = true
    · exact ⟨n, by rw [scan, if_pos hb]⟩
    · have hne : j ≠ n := by
        intro he
        subst j
        exact hb hp
      have hj' : j < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hne
      obtain ⟨i, hi⟩ := ih ⟨j, hj', hp⟩
      exact ⟨i, by rw [scan, if_neg hb]; exact hi⟩

structure Tower where
  bound : Nat → Nat
  valid : Nat → Nat → Bool
  proj : Nat → Nat → Nat → Nat

def Tower.Mem (T : Tower) (n a : Nat) : Prop :=
  a < T.bound n ∧ T.valid n a = true

structure Laws (T : Tower) : Prop where
  typed : ∀ n m z, n ≤ m → T.Mem m z → T.Mem n (T.proj n m z)
  ident : ∀ n z, T.Mem n z → T.proj n n z = z
  comp : ∀ n j m z, n ≤ j → j ≤ m → T.Mem m z →
    T.proj n j (T.proj j m z) = T.proj n m z

def Tower.Image (T : Tower) (n m a : Nat) : Prop :=
  ∃ z, T.Mem m z ∧ T.proj n m z = a

def cap (s : Nat → Nat) (n : Nat) : Nat :=
  if s n ≤ s (n+1) then s (n+1) else s n

theorem cap_left (s : Nat → Nat) (n : Nat) : s n ≤ cap s n := by
  unfold cap
  split
  next h => exact h
  next _ => exact Nat.le_refl _

theorem cap_right (s : Nat → Nat) (n : Nat) : s (n+1) ≤ cap s n := by
  unfold cap
  split
  next _ => exact Nat.le_refl _
  next h => exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem exists_steps {n t : Nat} (h : n ≤ t) : ∃ j, n + j = t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨j+1, congrArg Nat.succ hj⟩

def Local (T : Tower) (s : Nat → Nat) : Prop :=
  ∀ n a, T.Image n (s n) a → T.Image n (cap s n) a

def imageTest (T : Tower) (n m a z : Nat) : Bool :=
  if T.valid m z = true then decide (T.proj n m z = a) else false

def witness (T : Tower) (n m a : Nat) : Nat :=
  (scan (imageTest T n m a) (T.bound m)).getD 0

theorem witness_spec (T : Tower) (n m a : Nat) (h : T.Image n m a) :
    T.Mem m (witness T n m a) ∧ T.proj n m (witness T n m a) = a := by
  obtain ⟨z, ⟨hz, hv⟩, he⟩ := h
  have hw : ∃ j, j < T.bound m ∧ imageTest T n m a j = true :=
    ⟨z, hz, by rw [imageTest, if_pos hv]; exact decide_eq_true he⟩
  obtain ⟨j, hj⟩ := scan_complete _ _ hw
  obtain ⟨hlt, htest⟩ := scan_sound _ _ _ hj
  have hp : T.valid m j = true ∧ T.proj n m j = a := by
    by_cases hvj : T.valid m j = true
    · rw [imageTest, if_pos hvj] at htest
      exact ⟨hvj, of_decide_eq_true htest⟩
    · rw [imageTest, if_neg hvj] at htest
      cases htest
  have hs : witness T n m a = j := by rw [witness, hj]; rfl
  rw [hs]
  exact ⟨⟨hlt, hp.1⟩, hp.2⟩

def lift (T : Tower) (s : Nat → Nat) (n a : Nat) : Nat :=
  T.proj (n+1) (cap s n) (witness T n (cap s n) a)

theorem lift_spec (T : Tower) (L : Laws T) (s : Nat → Nat)
    (rate : ∀ j, j ≤ s j) (ok : Local T s)
    (n a : Nat) (h : T.Image n (s n) a) :
    T.Image (n+1) (s (n+1)) (lift T s n a) ∧
    T.proj n (n+1) (lift T s n a) = a := by
  let k := cap s n
  let z := witness T n k a
  have hks : s (n+1) ≤ k := cap_right s n
  have hn : n+1 ≤ s (n+1) := rate _
  have hnk : n+1 ≤ k := Nat.le_trans hn hks
  have hw : T.Mem k z ∧ T.proj n k z = a := witness_spec _ _ _ _ (ok n a h)
  change T.Image (n+1) (s (n+1)) (T.proj (n+1) k z) ∧
    T.proj n (n+1) (T.proj (n+1) k z) = a
  constructor
  · exact ⟨T.proj (s (n+1)) k z, L.typed _ _ _ hks hw.1,
           L.comp _ _ _ _ hn hks hw.1⟩
  · exact (L.comp _ _ _ _ (Nat.le_succ _) hnk hw.1).trans hw.2

def walk (T : Tower) (s : Nat → Nat) (n a : Nat) : Nat → Nat
  | 0 => a
  | j+1 => lift T s (n+j) (walk T s n a j)

theorem walk_image (T : Tower) (L : Laws T) (s : Nat → Nat)
    (rate : ∀ n, n ≤ s n) (ok : Local T s) (n a : Nat)
    (ha : T.Image n (s n) a) (j : Nat) :
    T.Image (n+j) (s (n+j)) (walk T s n a j) := by
  induction j with
  | zero => exact ha
  | succ j ih => exact (lift_spec T L s rate ok (n+j) _ ih).1

theorem walk_edge (T : Tower) (L : Laws T) (s : Nat → Nat)
    (rate : ∀ n, n ≤ s n) (ok : Local T s) (n a : Nat)
    (ha : T.Image n (s n) a) (j : Nat) :
    T.proj (n+j) ((n+j)+1) (walk T s n a (j+1)) = walk T s n a j :=
  (lift_spec T L s rate ok (n+j) _ (walk_image T L s rate ok n a ha j)).2

theorem image_typed (T : Tower) (L : Laws T) {n m a : Nat}
    (hnm : n ≤ m) (ha : T.Image n m a) : T.Mem n a := by
  obtain ⟨z, hz, he⟩ := ha
  exact he ▸ L.typed n m z hnm hz

theorem walk_proj (T : Tower) (L : Laws T) (s : Nat → Nat)
    (rate : ∀ n, n ≤ s n) (ok : Local T s) (n a : Nat)
    (ha : T.Image n (s n) a) (j : Nat) :
    T.proj n (n+j) (walk T s n a j) = a := by
  induction j with
  | zero => exact L.ident n a (image_typed T L (rate n) ha)
  | succ j ih =>
    have hm := image_typed T L (rate _) (walk_image T L s rate ok n a ha (j+1))
    have hc := L.comp n (n+j) (n+(j+1)) (walk T s n a (j+1))
      (Nat.le_add_right _ _) (Nat.le_succ _) hm
    have he := walk_edge T L s rate ok n a ha j
    exact hc.symm.trans ((congrArg (T.proj n (n+j)) he).trans ih)

theorem local_iff_stable (T : Tower) (L : Laws T) (s : Nat → Nat)
    (rate : ∀ j, j ≤ s j) :
    Local T s ↔ ∀ n t a, s n ≤ t → (T.Image n t a ↔ T.Image n (s n) a) := by
  constructor
  · intro ok n t a hst
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨T.proj (s n) t z, L.typed _ _ _ hst hz,
             (L.comp _ _ _ _ (rate n) hst hz).trans he⟩
    · intro ha
      have hnt := rate n
      obtain ⟨j, hsum⟩ := exists_steps (Nat.le_trans hnt hst)
      let w := walk T s n a j
      have hm : T.Mem (n+j) w :=
        image_typed T L (rate _) (walk_image T L s rate ok n a ha j)
      have he : T.proj n (n+j) w = a :=
        walk_proj T L s rate ok n a ha j
      exact ⟨w, hsum ▸ hm, hsum ▸ he⟩
  · intro st n a ha
    exact (st n (cap s n) a (cap_left s n)).2 ha

end IPRAReport.CategoryCase

#print axioms IPRAReport.CategoryCase.local_iff_stable
#print axioms IPRAReport.CategoryCase.walk_proj
