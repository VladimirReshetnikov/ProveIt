import DiophantineConsistency.ObjectCodeClosure

/-!
# The syntactic variable bound on internal formula codes

A certificate records pairs of a formula code and its bound. Every recorded
pair obeys one constructor equation. Totality and functionality use the
definable formula-code induction principle, so they apply to nonstandard codes.
The resulting bound agrees exactly with `SetTheory.bound` on quotations.
-/

namespace DiophantineConsistency.ObjectCodeBound

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectArithmetic

set_option maxRecDepth 14000
attribute [local irreducible] SetTheory.sealF

universe u
variable {V : Type u} {mem : V → V → Prop}

def BoundAtom (H : ZFAxioms mem) (c b : V) (t : Nat) : Prop :=
  ∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
    c = kpair H (natV H t) (kpair H i j) ∧
    AddRel H (vsucc H i) (vsucc H j) b

def BoundBinary (H : ZFAxioms mem) (S c b : V) (t : Nat) : Prop :=
  ∃ a d a' d', c = kpair H (natV H t) (kpair H a d) ∧
    mem (kpair H a a') S ∧ mem (kpair H d d') S ∧ AddRel H a' d' b

def BoundQuantifier (H : ZFAxioms mem) (S c b : V) (t : Nat) : Prop :=
  ∃ a, c = kpair H (natV H t) a ∧ mem (kpair H a b) S

def BoundStep (H : ZFAxioms mem) (S c b : V) : Prop :=
  BoundAtom H c b 0 ∨ BoundAtom H c b 1 ∨
    (c = formCode H fBot ∧ b = vempty H) ∨
    BoundBinary H S c b 3 ∨ BoundBinary H S c b 4 ∨ BoundBinary H S c b 5 ∨
    BoundQuantifier H S c b 6 ∨ BoundQuantifier H S c b 7

/-- Every pair in the certificate obeys a constructor equation using that graph. -/
def BoundClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ c b, mem (kpair H c b) S → mem b (omegaV H) ∧ BoundStep H S c b

/-- The internally computed syntactic bound. -/
def BoundCodeRel (H : ZFAxioms mem) (c b : V) : Prop :=
  ∃ S, BoundClosed H S ∧ mem (kpair H c b) S

theorem boundStep_mono (H : ZFAxioms mem) {S S' c b : V}
    (hsub : Sub mem S S') (h : BoundStep H S c b) : BoundStep H S' c b := by
  rcases h with h | h | h | ⟨a, d, a', d', hc, m1, m2, ha⟩ |
    ⟨a, d, a', d', hc, m1, m2, ha⟩ | ⟨a, d, a', d', hc, m1, m2, ha⟩ |
    ⟨a, hc, hm⟩ | ⟨a, hc, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, d, a', d', hc, hsub _ m1, hsub _ m2, ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, d, a', d', hc, hsub _ m1, hsub _ m2, ha⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, d, a', d', hc, hsub _ m1, hsub _ m2, ha⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hc, hsub _ hm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hc, hsub _ hm⟩))))))

theorem boundClosed_empty (H : ZFAxioms mem) : BoundClosed H (vempty H) :=
  fun _ _ h => absurd h (vempty_spec H _)

theorem boundClosed_cup (H : ZFAxioms mem) {S S' : V}
    (hS : BoundClosed H S) (hS' : BoundClosed H S') : BoundClosed H (vcup H S S') := by
  intro c b hm
  rcases (vcup_spec H S S' _).mp hm with h | h
  · exact ⟨(hS c b h).1,
      boundStep_mono H (fun x hx => (vcup_spec H S S' x).mpr (Or.inl hx)) (hS c b h).2⟩
  · exact ⟨(hS' c b h).1,
      boundStep_mono H (fun x hx => (vcup_spec H S S' x).mpr (Or.inr hx)) (hS' c b h).2⟩

theorem boundClosed_insert (H : ZFAxioms mem) {S c b : V}
    (hS : BoundClosed H S) (hb : mem b (omegaV H)) (hs : BoundStep H S c b) :
    BoundClosed H (vcup H S (vsingle H (kpair H c b))) := by
  have hsub : Sub mem S (vcup H S (vsingle H (kpair H c b))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro d e hm
  rcases (vcup_spec H S (vsingle H (kpair H c b)) _).mp hm with h | h
  · exact ⟨(hS d e h).1, boundStep_mono H hsub (hS d e h).2⟩
  · obtain ⟨hd, he⟩ := kpair_inj H _ _ _ _ ((vsingle_spec H _ _).mp h)
    rw [hd, he]
    exact ⟨hb, boundStep_mono H hsub hs⟩

theorem boundCodeRel_of_step (H : ZFAxioms mem) {S c b : V}
    (hS : BoundClosed H S) (hb : mem b (omegaV H)) (hs : BoundStep H S c b) :
    BoundCodeRel H c b :=
  ⟨vcup H S (vsingle H (kpair H c b)), boundClosed_insert H hS hb hs,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

theorem boundCodeRel_nat (H : ZFAxioms mem) {c b : V}
    (h : BoundCodeRel H c b) : mem b (omegaV H) := by
  obtain ⟨S, hS, hm⟩ := h
  exact (hS c b hm).1

theorem boundCodeRel_atom (H : ZFAxioms mem) (t : Nat) (ht : t = 0 ∨ t = 1)
    {i j b : V} (hi : mem i (omegaV H)) (hj : mem j (omegaV H))
    (ha : AddRel H (vsucc H i) (vsucc H j) b) :
    BoundCodeRel H (kpair H (natV H t) (kpair H i j)) b := by
  apply boundCodeRel_of_step H (boundClosed_empty H) (addRel_result_nat H ha)
  rcases ht with rfl | rfl
  · exact Or.inl ⟨i, j, hi, hj, rfl, ha⟩
  · exact Or.inr (Or.inl ⟨i, j, hi, hj, rfl, ha⟩)

theorem boundCodeRel_bot (H : ZFAxioms mem) :
    BoundCodeRel H (formCode H fBot) (vempty H) :=
  boundCodeRel_of_step H (boundClosed_empty H) (vempty_in_omega H)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem boundCodeRel_binary (H : ZFAxioms mem) (t : Nat)
    (ht : t = 3 ∨ t = 4 ∨ t = 5) {a d a' d' b : V}
    (h1 : BoundCodeRel H a a') (h2 : BoundCodeRel H d d') (ha : AddRel H a' d' b) :
    BoundCodeRel H (kpair H (natV H t) (kpair H a d)) b := by
  obtain ⟨S1, hS1, m1⟩ := h1
  obtain ⟨S2, hS2, m2⟩ := h2
  apply boundCodeRel_of_step H (boundClosed_cup H hS1 hS2) (addRel_result_nat H ha)
  have h : BoundBinary H (vcup H S1 S2)
      (kpair H (natV H t) (kpair H a d)) b t :=
    ⟨a, d, a', d', rfl, (vcup_spec H _ _ _).mpr (Or.inl m1),
      (vcup_spec H _ _ _).mpr (Or.inr m2), ha⟩
  rcases ht with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem boundCodeRel_quantifier (H : ZFAxioms mem) (t : Nat) (ht : t = 6 ∨ t = 7)
    {a b : V} (h : BoundCodeRel H a b) : BoundCodeRel H (kpair H (natV H t) a) b := by
  have hb := boundCodeRel_nat H h
  obtain ⟨S, hS, hm⟩ := h
  apply boundCodeRel_of_step H hS hb
  rcases ht with rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl, hm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl, hm⟩))))))

/-! ## Exact object-language graphs -/

def boundAtomForm (c b t : Nat) : Form :=
  fEx (fEx (fEx (fEx
    (fAnd (fNatF 3) (fAnd (fNatF 2)
      (fAnd (fTagPairF (c+4) t 3 2)
        (fAnd (fSuccF 1 3) (fAnd (fSuccF 0 2) (addForm (b+4) 1 0)))))))))

theorem boundAtomForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c b t : Nat) :
    Sat mem ee (boundAtomForm c b t) ↔ BoundAtom H (ee c) (ee b) t := by
  constructor
  · rintro ⟨i, j, si, sj, hi, hj, hc, hsi, hsj, ha⟩
    have hsi' : si = vsucc H i := (fSuccF_spec H _ 1 3).mp hsi
    have hsj' : sj = vsucc H j := (fSuccF_spec H _ 0 2).mp hsj
    have ha' := (addForm_spec H _ (b+4) 1 0).mp ha
    rw [hsi', hsj'] at ha'
    exact ⟨i, j, (fNatF_spec H _ 3).mp hi, (fNatF_spec H _ 2).mp hj,
      (fTagPairF_spec H _ (c+4) t 3 2).mp hc, ha'⟩
  · rintro ⟨i, j, hi, hj, hc, ha⟩
    exact ⟨i, j, vsucc H i, vsucc H j, (fNatF_spec H _ 3).mpr hi,
      (fNatF_spec H _ 2).mpr hj, (fTagPairF_spec H _ (c+4) t 3 2).mpr hc,
      (fSuccF_spec H _ 1 3).mpr rfl, (fSuccF_spec H _ 0 2).mpr rfl,
      (addForm_spec H _ (b+4) 1 0).mpr ha⟩

def boundBinaryForm (c b s t : Nat) : Form :=
  fEx (fEx (fEx (fEx
    (fAnd (fTagPairF (c+4) t 3 2)
      (fAnd (fPairMemF 3 1 (s+4))
        (fAnd (fPairMemF 2 0 (s+4)) (addForm (b+4) 1 0)))))))

theorem boundBinaryForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c b s t : Nat) :
    Sat mem ee (boundBinaryForm c b s t) ↔ BoundBinary H (ee s) (ee c) (ee b) t := by
  constructor
  · rintro ⟨a, d, a', d', hc, m1, m2, ha⟩
    exact ⟨a, d, a', d', (fTagPairF_spec H _ (c+4) t 3 2).mp hc,
      (fPairMemF_spec H _ 3 1 (s+4)).mp m1, (fPairMemF_spec H _ 2 0 (s+4)).mp m2,
      (addForm_spec H _ (b+4) 1 0).mp ha⟩
  · rintro ⟨a, d, a', d', hc, m1, m2, ha⟩
    exact ⟨a, d, a', d', (fTagPairF_spec H _ (c+4) t 3 2).mpr hc,
      (fPairMemF_spec H _ 3 1 (s+4)).mpr m1, (fPairMemF_spec H _ 2 0 (s+4)).mpr m2,
      (addForm_spec H _ (b+4) 1 0).mpr ha⟩

def boundQuantifierForm (c b s t : Nat) : Form :=
  fEx (fAnd (fTagUnF (c+1) t 0) (fPairMemF 0 (b+1) (s+1)))

theorem boundQuantifierForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c b s t : Nat) :
    Sat mem ee (boundQuantifierForm c b s t) ↔ BoundQuantifier H (ee s) (ee c) (ee b) t := by
  constructor
  · rintro ⟨a, hc, hm⟩
    exact ⟨a, (fTagUnF_spec H _ (c+1) t 0).mp hc,
      (fPairMemF_spec H _ 0 (b+1) (s+1)).mp hm⟩
  · rintro ⟨a, hc, hm⟩
    exact ⟨a, (fTagUnF_spec H _ (c+1) t 0).mpr hc,
      (fPairMemF_spec H _ 0 (b+1) (s+1)).mpr hm⟩

def boundStepForm (c b s : Nat) : Form :=
  fOr (boundAtomForm c b 0) (fOr (boundAtomForm c b 1)
    (fOr (fAnd (fTaggedEmptyF c 2) (fEmptyF b))
      (fOr (boundBinaryForm c b s 3) (fOr (boundBinaryForm c b s 4)
        (fOr (boundBinaryForm c b s 5)
          (fOr (boundQuantifierForm c b s 6) (boundQuantifierForm c b s 7)))))))

theorem boundStepForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c b s : Nat) :
    Sat mem ee (boundStepForm c b s) ↔ BoundStep H (ee s) (ee c) (ee b) :=
  or_congr (boundAtomForm_spec H ee c b 0)
    (or_congr (boundAtomForm_spec H ee c b 1)
      (or_congr (and_congr (fTaggedEmptyF_spec H ee c 2) (fEmptyF_spec H ee b))
        (or_congr (boundBinaryForm_spec H ee c b s 3)
          (or_congr (boundBinaryForm_spec H ee c b s 4)
            (or_congr (boundBinaryForm_spec H ee c b s 5)
              (or_congr (boundQuantifierForm_spec H ee c b s 6)
                (boundQuantifierForm_spec H ee c b s 7)))))))

def boundClosedForm (s : Nat) : Form :=
  fAll (fAll (fImp (fPairMemF 1 0 (s+2))
    (fAnd (fNatF 0) (boundStepForm 1 0 (s+2)))))

theorem boundClosedForm_spec (H : ZFAxioms mem) (ee : Nat → V) (s : Nat) :
    Sat mem ee (boundClosedForm s) ↔ BoundClosed H (ee s) := by
  constructor
  · intro h c b hm
    obtain ⟨hn, hs⟩ := h c b ((fPairMemF_spec H _ 1 0 (s+2)).mpr hm)
    exact ⟨(fNatF_spec H _ 0).mp hn, (boundStepForm_spec H _ 1 0 (s+2)).mp hs⟩
  · intro h c b hm
    obtain ⟨hn, hs⟩ := h c b ((fPairMemF_spec H _ 1 0 (s+2)).mp hm)
    exact ⟨(fNatF_spec H _ 0).mpr hn, (boundStepForm_spec H _ 1 0 (s+2)).mpr hs⟩

def boundCodeForm (b c : Nat) : Form :=
  fEx (fAnd (boundClosedForm 0) (fPairMemF (c+1) (b+1) 0))

theorem boundCodeForm_spec (H : ZFAxioms mem) (ee : Nat → V) (b c : Nat) :
    Sat mem ee (boundCodeForm b c) ↔ BoundCodeRel H (ee c) (ee b) := by
  constructor
  · rintro ⟨S, hS, hm⟩
    exact ⟨S, (boundClosedForm_spec H _ 0).mp hS,
      (fPairMemF_spec H _ (c+1) (b+1) 0).mp hm⟩
  · rintro ⟨S, hS, hm⟩
    exact ⟨S, (boundClosedForm_spec H _ 0).mpr hS,
      (fPairMemF_spec H _ (c+1) (b+1) 0).mpr hm⟩

/-! ## Inversion and functionality -/

theorem boundCodeRel_atom_inv (H : ZFAxioms mem) (t : Nat) (ht : t ≤ 1)
    {i j b : V} (h : BoundCodeRel H (kpair H (natV H t) (kpair H i j)) b) :
    AddRel H (vsucc H i) (vsucc H j) b := by
  obtain ⟨S, hS, hm⟩ := h
  have hs := (hS _ _ hm).2
  rcases hs with ⟨x, y, _, _, hc, ha⟩ | ⟨x, y, _, _, hc, ha⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · obtain ⟨_, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hi, hj]
    exact ha
  · obtain ⟨_, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hi, hj]
    exact ha
  all_goals exact absurd hc (formCode_tag_ne H (by omega) _ _)

theorem boundCodeRel_bot_inv (H : ZFAxioms mem) {b : V}
    (h : BoundCodeRel H (formCode H fBot) b) : b = vempty H := by
  obtain ⟨S, hS, hm⟩ := h
  have hs := (hS _ _ hm).2
  rcases hs with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨_, hb⟩ |
    ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact hb
  all_goals exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem boundCodeRel_binary_inv (H : ZFAxioms mem) (t : Nat)
    (ht : 3 ≤ t ∧ t ≤ 5) {a d b : V}
    (h : BoundCodeRel H (kpair H (natV H t) (kpair H a d)) b) :
    ∃ a' d', BoundCodeRel H a a' ∧ BoundCodeRel H d d' ∧ AddRel H a' d' b := by
  obtain ⟨S, hS, hm⟩ := h
  have hs := (hS _ _ hm).2
  rcases hs with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨x, y, a', d', hc, m1, m2, ha⟩ | ⟨x, y, a', d', hc, m1, m2, ha⟩ |
    ⟨x, y, a', d', hc, m1, m2, ha⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · obtain ⟨_, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1] at m1
    rw [← h2] at m2
    exact ⟨a', d', ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, ha⟩
  · obtain ⟨_, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1] at m1
    rw [← h2] at m2
    exact ⟨a', d', ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, ha⟩
  · obtain ⟨_, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1] at m1
    rw [← h2] at m2
    exact ⟨a', d', ⟨S, hS, m1⟩, ⟨S, hS, m2⟩, ha⟩
  all_goals exact absurd hc (formCode_tag_ne H (by omega) _ _)

theorem boundCodeRel_quantifier_inv (H : ZFAxioms mem) (t : Nat)
    (ht : 6 ≤ t ∧ t ≤ 7) {a b : V}
    (h : BoundCodeRel H (kpair H (natV H t) a) b) : BoundCodeRel H a b := by
  obtain ⟨S, hS, hm⟩ := h
  have hs := (hS _ _ hm).2
  rcases hs with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ |
    ⟨x, hc, hx⟩ | ⟨x, hc, hx⟩
  all_goals first
    | exact absurd hc (formCode_tag_ne H (by omega) _ _)
    | have he := (kpair_inj H _ _ _ _ hc).2
      rw [← he] at hx
      exact ⟨S, hS, hx⟩

private def totalAtForm : Form := fEx (boundCodeForm 0 1)

private theorem totalAtForm_spec (H : ZFAxioms mem) (c : V) :
    Sat mem (scons c (fun _ => vempty H)) totalAtForm ↔ ∃ b, BoundCodeRel H c b := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨b, (boundCodeForm_spec H _ 0 1).mp h⟩
  · rintro ⟨b, h⟩
    exact ⟨b, (boundCodeForm_spec H _ 0 1).mpr h⟩

/-- Every internal formula code, including every nonstandard one, has a bound. -/
theorem boundCodeRel_total (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → ∃ b, BoundCodeRel H c b := by
  refine isFormCodeSem_ind' H (fun c => ∃ b, BoundCodeRel H c b)
    totalAtForm (fun _ => vempty H) (fun c => (totalAtForm_spec H c).symm)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj
    obtain ⟨b, hb⟩ := addRel_total H (omega_succ H i hi) (omega_succ H j hj)
    exact ⟨b, boundCodeRel_atom H 0 (Or.inl rfl) hi hj hb⟩
  · intro i j hi hj
    obtain ⟨b, hb⟩ := addRel_total H (omega_succ H i hi) (omega_succ H j hj)
    exact ⟨b, boundCodeRel_atom H 1 (Or.inr rfl) hi hj hb⟩
  · exact ⟨_, boundCodeRel_bot H⟩
  · rintro a d ⟨a', ha⟩ ⟨d', hd⟩
    obtain ⟨b, hb⟩ := addRel_total H (boundCodeRel_nat H ha) (boundCodeRel_nat H hd)
    exact ⟨b, boundCodeRel_binary H 3 (Or.inl rfl) ha hd hb⟩
  · rintro a d ⟨a', ha⟩ ⟨d', hd⟩
    obtain ⟨b, hb⟩ := addRel_total H (boundCodeRel_nat H ha) (boundCodeRel_nat H hd)
    exact ⟨b, boundCodeRel_binary H 4 (Or.inr (Or.inl rfl)) ha hd hb⟩
  · rintro a d ⟨a', ha⟩ ⟨d', hd⟩
    obtain ⟨b, hb⟩ := addRel_total H (boundCodeRel_nat H ha) (boundCodeRel_nat H hd)
    exact ⟨b, boundCodeRel_binary H 5 (Or.inr (Or.inr rfl)) ha hd hb⟩
  · rintro a ⟨b, hb⟩
    exact ⟨b, boundCodeRel_quantifier H 6 (Or.inl rfl) hb⟩
  · rintro a ⟨b, hb⟩
    exact ⟨b, boundCodeRel_quantifier H 7 (Or.inr rfl) hb⟩

private def UniqueAt (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ b b', BoundCodeRel H c b → BoundCodeRel H c b' → b = b'

private def uniqueAtForm : Form :=
  fAll (fAll (fImp (boundCodeForm 1 2) (fImp (boundCodeForm 0 2) (fEq 1 0))))

private theorem uniqueAtForm_spec (H : ZFAxioms mem) (c : V) :
    Sat mem (scons c (fun _ => vempty H)) uniqueAtForm ↔ UniqueAt H c := by
  constructor
  · intro h b b' hb hb'
    exact h b b' ((boundCodeForm_spec H _ 1 2).mpr hb)
      ((boundCodeForm_spec H _ 0 2).mpr hb')
  · intro h b b' hb hb'
    exact h b b' ((boundCodeForm_spec H _ 1 2).mp hb)
      ((boundCodeForm_spec H _ 0 2).mp hb')

/-- The bound is single-valued on the whole internal formula-code predicate. -/
theorem boundCodeRel_unique (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → ∀ b b', BoundCodeRel H c b → BoundCodeRel H c b' → b = b' := by
  refine isFormCodeSem_ind' H (UniqueAt H) uniqueAtForm (fun _ => vempty H)
    (fun c => (uniqueAtForm_spec H c).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j _ _ b b' hb hb'
    exact addRel_unique H (boundCodeRel_atom_inv H 0 (by decide) hb)
      (boundCodeRel_atom_inv H 0 (by decide) hb')
  · intro i j _ _ b b' hb hb'
    exact addRel_unique H (boundCodeRel_atom_inv H 1 (by decide) hb)
      (boundCodeRel_atom_inv H 1 (by decide) hb')
  · intro b b' hb hb'
    exact (boundCodeRel_bot_inv H hb).trans (boundCodeRel_bot_inv H hb').symm
  · intro a d ha hd b b' hb hb'
    obtain ⟨a1, d1, ha1, hd1, hab⟩ := boundCodeRel_binary_inv H 3 (by decide) hb
    obtain ⟨a2, d2, ha2, hd2, hab'⟩ := boundCodeRel_binary_inv H 3 (by decide) hb'
    have hea := ha a1 a2 ha1 ha2
    have hed := hd d1 d2 hd1 hd2
    rw [← hea, ← hed] at hab'
    exact addRel_unique H hab hab'
  · intro a d ha hd b b' hb hb'
    obtain ⟨a1, d1, ha1, hd1, hab⟩ := boundCodeRel_binary_inv H 4 (by decide) hb
    obtain ⟨a2, d2, ha2, hd2, hab'⟩ := boundCodeRel_binary_inv H 4 (by decide) hb'
    have hea := ha a1 a2 ha1 ha2
    have hed := hd d1 d2 hd1 hd2
    rw [← hea, ← hed] at hab'
    exact addRel_unique H hab hab'
  · intro a d ha hd b b' hb hb'
    obtain ⟨a1, d1, ha1, hd1, hab⟩ := boundCodeRel_binary_inv H 5 (by decide) hb
    obtain ⟨a2, d2, ha2, hd2, hab'⟩ := boundCodeRel_binary_inv H 5 (by decide) hb'
    have hea := ha a1 a2 ha1 ha2
    have hed := hd d1 d2 hd1 hd2
    rw [← hea, ← hed] at hab'
    exact addRel_unique H hab hab'
  · intro a ha b b' hb hb'
    exact ha b b' (boundCodeRel_quantifier_inv H 6 (by decide) hb)
      (boundCodeRel_quantifier_inv H 6 (by decide) hb')
  · intro a ha b b' hb hb'
    exact ha b b' (boundCodeRel_quantifier_inv H 7 (by decide) hb)
      (boundCodeRel_quantifier_inv H 7 (by decide) hb')

/-- Exact agreement with the external bound, including its deliberately coarse
sum-of-indices convention. -/
theorem boundCodeRel_quotation (H : ZFAxioms mem) (f : Form) :
    BoundCodeRel H (formCode H f) (natV H (bound f)) := by
  induction f with
  | fMem i j =>
    exact boundCodeRel_atom H 0 (Or.inl rfl) (natV_mem_omega H i) (natV_mem_omega H j)
      (by simpa only [bound, natV_succ] using addRel_numerals H (i+1) (j+1))
  | fEq i j =>
    exact boundCodeRel_atom H 1 (Or.inr rfl) (natV_mem_omega H i) (natV_mem_omega H j)
      (by simpa only [bound, natV_succ] using addRel_numerals H (i+1) (j+1))
  | fBot => exact boundCodeRel_bot H
  | fImp a d ha hd =>
    exact boundCodeRel_binary H 3 (Or.inl rfl) ha hd (addRel_numerals H _ _)
  | fAnd a d ha hd =>
    exact boundCodeRel_binary H 4 (Or.inr (Or.inl rfl)) ha hd (addRel_numerals H _ _)
  | fOr a d ha hd =>
    exact boundCodeRel_binary H 5 (Or.inr (Or.inr rfl)) ha hd (addRel_numerals H _ _)
  | fAll a ha => exact boundCodeRel_quantifier H 6 (Or.inl rfl) ha
  | fEx a ha => exact boundCodeRel_quantifier H 7 (Or.inr rfl) ha

noncomputable def boundCodeValue (H : ZFAxioms mem) (c : V) : V := by
  classical
  exact if hc : IsFormCodeSem H c then (boundCodeRel_total H c hc).choose else vempty H

theorem boundCodeValue_spec (H : ZFAxioms mem) {c : V} (hc : IsFormCodeSem H c) :
    BoundCodeRel H c (boundCodeValue H c) := by
  classical
  simp only [boundCodeValue, dif_pos hc]
  exact (boundCodeRel_total H c hc).choose_spec

theorem boundCodeValue_nat (H : ZFAxioms mem) {c : V} (hc : IsFormCodeSem H c) :
    mem (boundCodeValue H c) (omegaV H) := boundCodeRel_nat H (boundCodeValue_spec H hc)

theorem boundCodeValue_quotation (H : ZFAxioms mem) (f : Form) :
    boundCodeValue H (formCode H f) = natV H (bound f) :=
  boundCodeRel_unique H _ (formCode_isFormCodeSem H f) _ _
    (boundCodeValue_spec H (formCode_isFormCodeSem H f)) (boundCodeRel_quotation H f)

def boundCodeTotalForm : Form := sealF
  (fAll (fImp (fIsFormCodeF 0) (fEx (boundCodeForm 0 1))))

theorem sentence_boundCodeTotalForm : Sentence boundCodeTotalForm := Sentence_seal _

def boundCodeUniqueForm : Form := sealF
  (fAll (fImp (fIsFormCodeF 0)
    (fAll (fAll (fImp (fAnd (boundCodeForm 1 2) (boundCodeForm 0 2)) (fEq 1 0))))))

theorem sentence_boundCodeUniqueForm : Sentence boundCodeUniqueForm := Sentence_seal _

theorem zfc_proves_boundCode_total : BProv ZFCax_s [] boundCodeTotalForm := by
  apply completeness_inf_context ZFCax_s [] boundCodeTotalForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' c hc
  have hc' : IsFormCodeSem H c := (fIsFormCodeF_spec H _ 0).mp hc
  obtain ⟨b, hb⟩ := boundCodeRel_total H c hc'
  exact ⟨b, (boundCodeForm_spec H _ 0 1).mpr hb⟩

theorem zfc_proves_boundCode_unique : BProv ZFCax_s [] boundCodeUniqueForm := by
  apply completeness_inf_context ZFCax_s [] boundCodeUniqueForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' c hc b b' h
  exact boundCodeRel_unique H c ((fIsFormCodeF_spec H _ 0).mp hc) b b'
    ((boundCodeForm_spec H _ 1 2).mp h.1) ((boundCodeForm_spec H _ 0 2).mp h.2)

end DiophantineConsistency.ObjectCodeBound
