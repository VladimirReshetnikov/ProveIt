/-
  Completeness.lean

  GENERIC Gödel/Henkin completeness for the calculus of Calculus.lean
  w.r.t. the Tarski semantics of Fol.lean — for ANY theory over this
  language, with no set-theoretic content whatsoever:

   - the quotient term model of an abstract maximal-consistent Henkin
     theory, and the TRUTH LEMMA (`model_exists`);
   - the B-relative Lindenbaum/Henkin chain over a sentence theory `B`
     plus a finite context: `BProv`, `model_of_BCon`;
   - COMPLETENESS `completeness` and `prov_iff_valid`
     (`Prov G phi ↔ G ⊨ phi`) — obtained from `model_of_BCon` at the
     EMPTY base theory `B = ∅` (`model_of_con` is that instance);
   - infinite-theory completeness for sentence theories
     (`completeness_inf`), one-way semantic proof transfer
     (`theory_transfer`), and DEDUCTIVE EQUIVALENCE `theory_equiv`:
     two sentence theories with the same models prove the same
     sentences — the abstract engine for proving any two
     axiomatizations deductively equivalent.

  Lean 4 port of the Rocq/Coq development `Logic/FirstOrder/Coq/Completeness.v`.
-/
import FirstOrder.Calculus

namespace SetTheory

open Form

/-! ### Hilbert epsilon (Coq: `ClassicalEpsilon.epsilon`) -/

open Classical in
noncomputable def epsilon {α : Sort u} [ne : Nonempty α] (p : α → Prop) : α :=
  if h : ∃ x, p x then h.choose else Classical.choice ne

theorem epsilon_spec {α : Sort u} [Nonempty α] {p : α → Prop} (h : ∃ x, p x) :
    p (epsilon p) := by
  unfold epsilon
  rw [dif_pos h]
  exact h.choose_spec

/-! ### Helpers to discharge "every element of an explicit context is in T"
(Coq: the `ctxT` tactic) -/

theorem mem_T_nil {T : Form → Prop} : ∀ x ∈ ([] : List Form), T x :=
  fun _ hx => nomatch hx

theorem mem_T_cons {T : Form → Prop} {a : Form} {G : List Form}
    (ha : T a) (hG : ∀ x ∈ G, T x) : ∀ x ∈ a :: G, T x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact hG x hx

/-! ## The canonical (quotient term) model of a maximal-consistent Henkin
theory -/

/-- A maximal-consistent Henkin theory (the five hypotheses of Coq's
`Section CanonicalModel`). -/
structure MCHT (T : Form → Prop) : Prop where
  cons : ¬ T fBot
  compl : ∀ phi, T phi ∨ T (fImp phi fBot)
  closed : ∀ G phi, (∀ x ∈ G, T x) → Prov G phi → T phi
  henkin_ex : ∀ a, T (fEx a) → ∃ k, T (rename (inst k) a)
  henkin_all : ∀ a, (∀ k, T (rename (inst k) a)) → T (fAll a)

section CanonicalModel

variable {T : Form → Prop}

theorem T_prov0 (h : MCHT T) (phi : Form) (hp : Prov [] phi) : T phi :=
  h.closed [] phi mem_T_nil hp

theorem T_mp (h : MCHT T) (a b : Form) (hab : T (fImp a b)) (ha : T a) : T b := by
  apply h.closed [fImp a b, a] b (mem_T_cons hab (mem_T_cons ha mem_T_nil))
  exact .P_impE _ a b (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))

theorem T_imp_iff (h : MCHT T) (a b : Form) : T (fImp a b) ↔ (T a → T b) := by
  constructor
  · intro hab ha; exact T_mp h a b hab ha
  · intro himp
    rcases h.compl a with ha | hna
    · apply h.closed [b] (fImp a b) (mem_T_cons (himp ha) mem_T_nil)
      exact .P_impI _ _ _ (.P_ass _ _ (by simp))
    · apply h.closed [fImp a fBot] (fImp a b) (mem_T_cons hna mem_T_nil)
      apply Prov.P_impI
      apply Prov.P_botE
      exact .P_impE _ a fBot (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))

theorem T_and_iff (h : MCHT T) (a b : Form) : T (fAnd a b) ↔ (T a ∧ T b) := by
  constructor
  · intro hab
    constructor
    · apply h.closed [fAnd a b] a (mem_T_cons hab mem_T_nil)
      exact .P_andE1 _ a b (.P_ass _ _ (by simp))
    · apply h.closed [fAnd a b] b (mem_T_cons hab mem_T_nil)
      exact .P_andE2 _ a b (.P_ass _ _ (by simp))
  · intro ⟨ha, hb⟩
    apply h.closed [a, b] (fAnd a b) (mem_T_cons ha (mem_T_cons hb mem_T_nil))
    exact .P_andI _ _ _ (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))

theorem T_or_iff (h : MCHT T) (a b : Form) : T (fOr a b) ↔ (T a ∨ T b) := by
  constructor
  · intro hab
    rcases h.compl a with ha | hna
    · exact Or.inl ha
    rcases h.compl b with hb | hnb
    · exact Or.inr hb
    exfalso
    apply h.cons
    apply h.closed [fOr a b, fImp a fBot, fImp b fBot] fBot
      (mem_T_cons hab (mem_T_cons hna (mem_T_cons hnb mem_T_nil)))
    apply Prov.P_orE _ a b fBot (.P_ass _ _ (by simp))
    · exact .P_impE _ a fBot (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))
    · exact .P_impE _ b fBot (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))
  · intro hab
    rcases hab with ha | hb
    · apply h.closed [a] (fOr a b) (mem_T_cons ha mem_T_nil)
      exact .P_orI1 _ _ _ (.P_ass _ _ (by simp))
    · apply h.closed [b] (fOr a b) (mem_T_cons hb mem_T_nil)
      exact .P_orI2 _ _ _ (.P_ass _ _ (by simp))

theorem T_all_iff (h : MCHT T) (a : Form) :
    T (fAll a) ↔ ∀ k, T (rename (inst k) a) := by
  constructor
  · intro ht k
    apply h.closed [fAll a] (rename (inst k) a) (mem_T_cons ht mem_T_nil)
    exact .P_allE _ a k (.P_ass _ _ (by simp))
  · exact h.henkin_all a

theorem T_ex_iff (h : MCHT T) (a : Form) :
    T (fEx a) ↔ ∃ k, T (rename (inst k) a) := by
  constructor
  · exact h.henkin_ex a
  · intro ⟨k, hk⟩
    apply h.closed [rename (inst k) a] (fEx a) (mem_T_cons hk mem_T_nil)
    exact .P_exI _ a k (.P_ass _ _ (by simp))

/-! ### The canonical equivalence on variables, and the quotient term model -/

def ceq (Th : Form → Prop) (i j : Nat) : Prop := Th (fEq i j)

def cmem (Th : Form → Prop) (i j : Nat) : Prop := Th (fMem i j)

theorem ceq_refl (h : MCHT T) (i : Nat) : ceq T i i :=
  T_prov0 h _ (.P_eqRefl _ i)

theorem ceq_sym (h : MCHT T) {i j : Nat} (hij : ceq T i j) : ceq T j i := by
  apply h.closed [fEq i j] (fEq j i) (mem_T_cons hij mem_T_nil)
  exact Prov_eq_sym _ i j (.P_ass _ _ (by simp))

theorem ceq_trans (h : MCHT T) {i j k : Nat} (h1 : ceq T i j) (h2 : ceq T j k) :
    ceq T i k := by
  apply h.closed [fEq i j, fEq j k] (fEq i k)
    (mem_T_cons h1 (mem_T_cons h2 mem_T_nil))
  exact Prov_eq_trans _ i j k (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))

theorem cmem_cong (h : MCHT T) {i i' j j' : Nat}
    (hi : ceq T i i') (hj : ceq T j j') (hm : cmem T i j) : cmem T i' j' := by
  apply h.closed [fEq i i', fEq j j', fMem i j] (fMem i' j')
    (mem_T_cons hi (mem_T_cons hj (mem_T_cons hm mem_T_nil)))
  apply Prov_mem_cong2 _ j j' i' (.P_ass _ _ (by simp))
  exact Prov_mem_cong1 _ i i' j (.P_ass _ _ (by simp)) (.P_ass _ _ (by simp))

/-! ### The quotient term model and the truth lemma -/

/-- Canonical representative of a `ceq`-class, via Hilbert epsilon. -/
noncomputable def rep (Th : Form → Prop) (i : Nat) : Nat :=
  epsilon (fun j => ceq Th i j)

theorem rep_ceq (h : MCHT T) (i : Nat) : ceq T i (rep T i) :=
  epsilon_spec ⟨i, ceq_refl h i⟩

theorem rep_respects (h : MCHT T) {i j : Nat} (hij : ceq T i j) :
    rep T i = rep T j := by
  unfold rep
  congr 1
  funext k
  exact propext ⟨fun hk => ceq_trans h (ceq_sym h hij) hk,
                 fun hk => ceq_trans h hij hk⟩

theorem rep_idem (h : MCHT T) (i : Nat) : rep T (rep T i) = rep T i :=
  rep_respects h (ceq_sym h (rep_ceq h i))

def D (Th : Form → Prop) : Type := { n : Nat // rep Th n = n }

noncomputable def mkD (h : MCHT T) (i : Nat) : D T := ⟨rep T i, rep_idem h i⟩

def memD (Th : Form → Prop) (x y : D Th) : Prop := cmem Th x.val y.val

theorem D_eq {x y : D T} (h : x.val = y.val) : x = y := Subtype.ext h

theorem mkD_proj (h : MCHT T) (x : D T) : mkD h x.val = x :=
  Subtype.ext x.property

private theorem canonical_scons (h : MCHT T) (d : D T) (k : Nat)
    (s : Nat → Nat) (hd : d = mkD h k) : ∀ n,
    scons d (fun i => mkD h (s i)) n =
      (fun i => mkD h (scons_nat k s i)) n :=
  fun n => match n with | 0 => hd | _+1 => rfl

/-- The truth lemma, by structural induction on the formula with the
substitution generalized (the quantifier cases recurse on the body at a
consed substitution, via `rename_inst_up`): under the canonical variable
assignment `i ↦ [s i]`, satisfaction matches membership in `T`. -/
theorem truth (h : MCHT T) :
    ∀ (a : Form) (s : Nat → Nat),
      Sat (memD T) (fun i => mkD h (s i)) a ↔ T (rename s a) := by
  intro a
  induction a with
  | fMem i j =>
    intro s
    show memD T (mkD h (s i)) (mkD h (s j)) ↔ T (fMem (s i) (s j))
    constructor
    · intro hm
      exact cmem_cong h (ceq_sym h (rep_ceq h (s i)))
        (ceq_sym h (rep_ceq h (s j))) hm
    · intro hm
      exact cmem_cong h (rep_ceq h (s i)) (rep_ceq h (s j)) hm
  | fEq i j =>
    intro s
    show mkD h (s i) = mkD h (s j) ↔ T (fEq (s i) (s j))
    constructor
    · intro he
      have hr : rep T (s i) = rep T (s j) := congrArg Subtype.val he
      exact ceq_trans h (hr ▸ rep_ceq h (s i)) (ceq_sym h (rep_ceq h (s j)))
    · intro he
      exact Subtype.ext (rep_respects h he)
  | fBot =>
    intro s
    exact ⟨False.elim, fun ht => absurd ht h.cons⟩
  | fImp a1 a2 IH1 IH2 =>
    intro s
    show (Sat (memD T) _ a1 → Sat (memD T) _ a2) ↔ T (fImp (rename s a1) (rename s a2))
    rw [IH1 s, IH2 s]
    exact (T_imp_iff h _ _).symm
  | fAnd a1 a2 IH1 IH2 =>
    intro s
    show (Sat (memD T) _ a1 ∧ Sat (memD T) _ a2) ↔ T (fAnd (rename s a1) (rename s a2))
    rw [IH1 s, IH2 s]
    exact (T_and_iff h _ _).symm
  | fOr a1 a2 IH1 IH2 =>
    intro s
    show (Sat (memD T) _ a1 ∨ Sat (memD T) _ a2) ↔ T (fOr (rename s a1) (rename s a2))
    rw [IH1 s, IH2 s]
    exact (T_or_iff h _ _).symm
  | fAll a1 IH =>
    intro s
    show (∀ d, Sat (memD T) (scons d _) a1) ↔ T (fAll (rename (up s) a1))
    constructor
    · intro HSat
      apply (T_all_iff h (rename (up s) a1)).mpr
      intro k
      rw [rename_inst_up a1 k s]
      apply (IH (scons_nat k s)).mp
      exact (Sat_ext a1 _ _ (canonical_scons h (mkD h k) k s rfl)).mp
        (HSat (mkD h k))
    · intro HT d
      have hk := (T_all_iff h (rename (up s) a1)).mp HT d.val
      rw [rename_inst_up a1 d.val s] at hk
      have hk' := (IH (scons_nat d.val s)).mpr hk
      exact (Sat_ext a1 _ _
        (canonical_scons h d d.val s (mkD_proj h d).symm)).mpr hk'
  | fEx a1 IH =>
    intro s
    show (∃ d, Sat (memD T) (scons d _) a1) ↔ T (fEx (rename (up s) a1))
    constructor
    · intro ⟨d, HSat⟩
      apply (T_ex_iff h (rename (up s) a1)).mpr
      refine ⟨d.val, ?_⟩
      rw [rename_inst_up a1 d.val s]
      apply (IH (scons_nat d.val s)).mp
      exact (Sat_ext a1 _ _
        (canonical_scons h d d.val s (mkD_proj h d).symm)).mp HSat
    · intro HT
      obtain ⟨k, hk⟩ := (T_ex_iff h (rename (up s) a1)).mp HT
      rw [rename_inst_up a1 k s] at hk
      have hk' := (IH (scons_nat k s)).mpr hk
      refine ⟨mkD h k, ?_⟩
      exact (Sat_ext a1 _ _ (canonical_scons h (mkD h k) k s rfl)).mpr hk'

/-- Canonical assignment: satisfaction matches `T` outright. -/
theorem truth_id (h : MCHT T) (a : Form) :
    Sat (memD T) (fun i => mkD h i) a ↔ T a := by
  have H := truth h a (fun i => i)
  rwa [rename_id] at H

/-- MODEL EXISTENCE: every maximal-consistent Henkin theory is satisfiable. -/
theorem model_exists (T : Form → Prop) (h : MCHT T) :
    ∃ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      ∀ a, Sat m v a ↔ T a :=
  ⟨D T, memD T, fun i => mkD h i, truth_id h⟩

end CanonicalModel

/-! ## The Lindenbaum/Henkin chain, relative to a SENTENCE base theory `B`.

A sentence has no free variables, so any variable is fresh w.r.t. the
(possibly infinite) base theory `B` — which is what lets the Henkin witnesses
work over an infinite theory.  Ordinary finite-context completeness is the
`B = ∅` instance (`BProv_empty` / `model_of_con` below). -/

/-- Robust membership solver for list app/cons rearrangements (Coq: `mem`). -/
macro "mem_tac" : tactic =>
  `(tactic| (intro x; simp only [List.mem_append, List.mem_cons]; grind))

/-- "`B` together with the finite list `G` proves `phi`". -/
def BProv (B : Form → Prop) (G : List Form) (phi : Form) : Prop :=
  ∃ Gb, (∀ x ∈ Gb, B x) ∧ Prov (Gb ++ G) phi

def BCon (B : Form → Prop) (G : List Form) : Prop := ¬ BProv B G fBot

theorem BProv_mono (B : Form → Prop) (G G' : List Form) (phi : Form)
    (hsub : ∀ x ∈ G, x ∈ G') (h : BProv B G phi) : BProv B G' phi := by
  obtain ⟨Gb, hGb, hp⟩ := h
  refine ⟨Gb, hGb, ?_⟩
  apply Prov_weaken hp
  exact List.forall_mem_append.mpr
    ⟨fun x hx => List.mem_append_left _ hx,
     fun x hx => List.mem_append_right _ (hsub x hx)⟩

/-- A theory axiom is relatively provable from that theory. -/
theorem BProv_ax {B : Form → Prop} {G : List Form} {phi : Form}
    (hphi : B phi) : BProv B G phi :=
  ⟨[phi], fun x hx => List.mem_singleton.mp hx ▸ hphi, .P_ass _ _ (by simp)⟩

/-- A bare finite-context proof is also a proof relative to any theory. -/
theorem BProv_of_Prov {B : Form → Prop} {G : List Form} {phi : Form}
    (h : Prov G phi) : BProv B G phi := by
  refine ⟨[], ?_, by simpa using h⟩
  intro x hx
  cases hx

/-- A finite-context assumption is available in relative provability. -/
theorem BProv_ass {B : Form → Prop} {G : List Form} {phi : Form}
    (hphi : phi ∈ G) : BProv B G phi :=
  BProv_of_Prov (B := B) (Prov.P_ass G phi hphi)

/-- A finite list of relative proofs can be put over one shared finite list of
theory axioms. -/
theorem BProv_bound_list (B : Form → Prop) (D : List Form) :
    ∀ L : List Form, (∀ x, x ∈ L → BProv B D x) →
      ∃ Lb, (∀ x, x ∈ Lb → B x) ∧
        ∀ x, x ∈ L → Prov (Lb ++ D) x := by
  intro L
  induction L with
  | nil =>
      intro _hL
      refine ⟨[], ?_, ?_⟩ <;> exact fun x hx => nomatch hx
  | cons a L ih =>
      intro hL
      rcases hL a (by simp) with ⟨La, hLa, hpa⟩
      rcases ih (fun x hx => hL x (by simp [hx])) with ⟨Lb, hLb, hpL⟩
      refine ⟨La ++ Lb, List.forall_mem_append.mpr ⟨hLa, hLb⟩, ?_⟩
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · apply Prov_weaken hpa
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inl hy))
          · exact Or.inr hy
        · apply Prov_weaken (hpL x hx)
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inr hy))
          · exact Or.inr hy

/-- Transport a relative proof to another theory/context once every used source
axiom and every finite-context assumption has been proved in the target. -/
theorem BProv_lift {B C : Form → Prop} {G D : List Form} {phi : Form}
    (h : BProv B G phi)
    (hB : ∀ b, B b → BProv C D b)
    (hG : ∀ g, g ∈ G → BProv C D g) : BProv C D phi := by
  rcases h with ⟨Lb, hLb, hp⟩
  have hctx : ∀ x, x ∈ Lb ++ G → BProv C D x :=
    List.forall_mem_append.mpr ⟨fun x hx => hB x (hLb x hx), hG⟩
  rcases BProv_bound_list C D (Lb ++ G) hctx with ⟨Lc, hLc, hpctx⟩
  refine ⟨Lc, hLc, ?_⟩
  exact Prov_cut hp (Lc ++ D) hpctx

/-- Relative provability is closed under cutting in proofs of the finite
context. -/
theorem BProv_cut {B : Form → Prop} {G D : List Form} {phi : Form}
    (h : BProv B G phi)
    (hG : ∀ g, g ∈ G → BProv B D g) : BProv B D phi :=
  BProv_lift h (fun _ hb => BProv_ax (G := D) hb) hG

/-- Lift an arbitrary finite natural-deduction derivation into relative
provability by supplying relative proofs of its assumptions.

This is the reusable closure principle behind the connective and equality
rules below; clients should not need to reopen and merge the finite lists of
background-theory axioms stored inside `BProv`. -/
theorem BProv_derive {B : Form → Prop} {G Δ : List Form} {phi : Form}
    (hp : Prov Δ phi)
    (hΔ : ∀ d, d ∈ Δ → BProv B G d) : BProv B G phi :=
  BProv_cut (BProv_of_Prov (B := B) hp) hΔ

/-- Lift a unary finite-context proof rule uniformly over relative
provability. -/
theorem BProv_rule1 {B : Form → Prop} {G : List Form} {a b : Form}
    (rule : ∀ Δ, Prov Δ a → Prov Δ b)
    (ha : BProv B G a) : BProv B G b := by
  rcases ha with ⟨L, hL, hp⟩
  exact ⟨L, hL, rule (L ++ G) hp⟩

/-- Lift a binary finite-context proof rule uniformly over relative
provability. -/
theorem BProv_rule2 {B : Form → Prop} {G : List Form} {a b c : Form}
    (rule : ∀ Δ, Prov Δ a → Prov Δ b → Prov Δ c)
    (ha : BProv B G a) (hb : BProv B G b) : BProv B G c := by
  apply BProv_derive
    (rule [a, b]
      (Prov.P_ass _ _ (by simp))
      (Prov.P_ass _ _ (by simp)))
  intro d hd
  simp at hd
  rcases hd with rfl | rfl
  · exact ha
  · exact hb

/-- Enlarging the background theory preserves relative provability. -/
theorem BProv_theory_mono {B C : Form → Prop} {G : List Form} {phi : Form}
    (hBC : ∀ b, B b → C b) (h : BProv B G phi) : BProv C G phi :=
  BProv_lift h
    (fun b hb => BProv_ax (G := G) (hBC b hb))
    (fun g hg => BProv_of_Prov (B := C) (Prov.P_ass G g hg))

/-- Relative provability is closed under the set-theory equality elimination
rule.  The formula `a` is the one-variable context, instantiated first by
`i` and then by `j`. -/
theorem BProv_eqElim {B : Form → Prop} {G : List Form} {i j : Nat}
    {a : Form}
    (heq : BProv B G (fEq i j))
    (ha : BProv B G (rename (inst i) a)) :
    BProv B G (rename (inst j) a) :=
  BProv_rule2 (fun Δ heq' ha' => Prov.P_eqElim Δ i j a heq' ha') heq ha

/-- Relative provability is closed under symmetry of equality. -/
theorem BProv_eqSym {B : Form → Prop} {G : List Form} {i j : Nat}
    (heq : BProv B G (fEq i j)) : BProv B G (fEq j i) :=
  BProv_rule1 (fun Δ heq' => Prov_eq_sym Δ i j heq') heq

/-- Relative provability is closed under transitivity of equality. -/
theorem BProv_eqTrans {B : Form → Prop} {G : List Form} {i j k : Nat}
    (hij : BProv B G (fEq i j)) (hjk : BProv B G (fEq j k)) :
    BProv B G (fEq i k) :=
  BProv_rule2 (fun Δ hij' hjk' => Prov_eq_trans Δ i j k hij' hjk') hij hjk

/-- Soundness for relative provability from a base theory and finite context. -/
theorem soundness_BProv {α : Type u} {mem : α → α → Prop} {B : Form → Prop}
    {G : List Form} {phi : Form} (h : BProv B G phi) (e : Nat → α)
    (hB : ∀ b, B b → Sat mem e b)
    (hG : ∀ g, g ∈ G → Sat mem e g) : Sat mem e phi := by
  rcases h with ⟨L, hL, hp⟩
  exact soundness hp e
    (List.forall_mem_append.mpr ⟨fun x hx => hB x (hL x hx), hG⟩)

theorem BCon_cons_or (B : Form → Prop) (L : List Form) (phi : Form)
    (hL : BCon B L) : BCon B (phi :: L) ∨ BCon B (fImp phi fBot :: L) := by
  rcases Classical.em (BCon B (phi :: L)) with h | h
  · exact Or.inl h
  right
  have h' : BProv B (phi :: L) fBot := Classical.byContradiction h
  obtain ⟨Gb1, hGb1, hbad1⟩ := h'
  intro ⟨Gb2, hGb2, hbad2⟩
  apply hL
  refine ⟨Gb1 ++ Gb2, List.forall_mem_append.mpr ⟨hGb1, hGb2⟩, ?_⟩
  · apply Prov.P_impE _ (fImp phi fBot) fBot
    · apply Prov.P_impI
      apply Prov_weaken (Prov_exch (G := Gb2 ++ fImp phi fBot :: L)
        (G' := fImp phi fBot :: (Gb2 ++ L)) (by mem_tac) hbad2)
      mem_tac
    · apply Prov.P_impI
      apply Prov_weaken (Prov_exch (G := Gb1 ++ phi :: L)
        (G' := phi :: (Gb1 ++ L)) (by mem_tac) hbad1)
      mem_tac

theorem BCon_henkin_ex (B : Form → Prop) (L : List Form) (a : Form)
    (hB : Sentences B) (hcon : BCon B (fEx a :: L)) :
    BCon B (rename (inst (freshFor (fEx a :: L))) a :: fEx a :: L) := by
  intro ⟨Gb, hGb, hbad⟩
  apply hcon
  refine ⟨Gb, hGb, ?_⟩
  apply Prov_exch (G := fEx a :: (Gb ++ L)) (by mem_tac)
  have hwa : ¬ Free (freshFor (fEx a :: L)) (fEx a) :=
    freshFor_not_free (List.mem_cons.mpr (Or.inl rfl))
  apply henkin_ex_core (Gb ++ L) a (freshFor (fEx a :: L)) hwa
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hB g (hGb g hg) _
    · exact freshFor_not_free (List.mem_cons.mpr (Or.inr hg))
  · exact Prov_exch (G := Gb ++ rename (inst (freshFor (fEx a :: L))) a :: fEx a :: L)
      (by mem_tac) hbad

theorem BCon_henkin_all (B : Form → Prop) (L : List Form) (a : Form)
    (hB : Sentences B) (hcon : BCon B (fImp (fAll a) fBot :: L)) :
    BCon B (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
            :: fImp (fAll a) fBot :: L) := by
  intro ⟨Gb, hGb, hbad⟩
  apply hcon
  refine ⟨Gb, hGb, ?_⟩
  apply Prov_exch (G := fImp (fAll a) fBot :: (Gb ++ L)) (by mem_tac)
  apply henkin_all_core (Gb ++ L) a (freshFor (fImp (fAll a) fBot :: L))
  · intro hf
    exact freshFor_not_free (L := fImp (fAll a) fBot :: L)
      (List.mem_cons.mpr (Or.inl rfl)) (Or.inl hf)
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hB g (hGb g hg) _
    · exact freshFor_not_free (List.mem_cons.mpr (Or.inr hg))
  · exact Prov_exch
      (G := Gb ++ fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
              :: fImp (fAll a) fBot :: L)
      (by mem_tac) hbad

/-! ### The B-relative Lindenbaum chain -/

open Classical in
noncomputable def stepB (B : Form → Prop) (L : List Form) (phi : Form) : List Form :=
  if BCon B (phi :: L) then
    match phi with
    | fEx a => rename (inst (freshFor (fEx a :: L))) a :: fEx a :: L
    | _ => phi :: L
  else
    match phi with
    | fAll a => fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
                :: fImp (fAll a) fBot :: L
    | _ => fImp phi fBot :: L

theorem stepB_con (B : Form → Prop) (L : List Form) (phi : Form)
    (hB : Sentences B) (hL : BCon B L) : BCon B (stepB B L phi) := by
  unfold stepB
  rcases Classical.em (BCon B (phi :: L)) with hc | hc
  · rw [if_pos hc]
    cases phi <;> first
      | exact hc
      | exact BCon_henkin_ex B L _ hB hc
  · rw [if_neg hc]
    rcases BCon_cons_or B L phi hL with hbad | hcn
    · exact absurd hbad hc
    · cases phi <;> first
        | exact hcn
        | exact BCon_henkin_all B L _ hB hcn

theorem stepB_incl (B : Form → Prop) (L : List Form) (phi x : Form)
    (hx : x ∈ L) : x ∈ stepB B L phi := by
  unfold stepB
  rcases Classical.em (BCon B (phi :: L)) with hc | hc
  · rw [if_pos hc]; cases phi <;> simp [hx]
  · rw [if_neg hc]; cases phi <;> simp [hx]

theorem stepB_decides (B : Form → Prop) (L : List Form) (phi : Form) :
    phi ∈ stepB B L phi ∨ (fImp phi fBot) ∈ stepB B L phi := by
  unfold stepB
  rcases Classical.em (BCon B (phi :: L)) with hc | hc
  · left; rw [if_pos hc]; cases phi <;> simp
  · right; rw [if_neg hc]; cases phi <;> simp

noncomputable def chainB (B : Form → Prop) (L0 : List Form) : Nat → List Form
  | 0 => L0
  | n+1 => stepB B (chainB B L0 n) (Enum n)

theorem chainB_incl (B : Form → Prop) (L0 : List Form) (m : Nat) (x : Form)
    (hx : x ∈ chainB B L0 m) : x ∈ chainB B L0 (m+1) :=
  stepB_incl B _ _ x hx

theorem chainB_mono (B : Form → Prop) (L0 : List Form) (n m : Nat) (hle : m ≤ n) :
    ∀ x ∈ chainB B L0 m, x ∈ chainB B L0 n := by
  induction n with
  | zero =>
    intro x hx
    have : m = 0 := by omega
    subst this; exact hx
  | succ n IHn =>
    intro x hx
    rcases Nat.le_succ_iff.mp hle with hle' | heq
    · exact chainB_incl B L0 n x (IHn hle' x hx)
    · subst heq; exact hx

theorem chainB_con (B : Form → Prop) (L0 : List Form)
    (hB : Sentences B) (h0 : BCon B L0) : ∀ n, BCon B (chainB B L0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n IHn => exact stepB_con B _ _ hB IHn

/-! ### The maximal-consistent Henkin theory over (B, L0), and completeness -/

def Tinf (B : Form → Prop) (L0 : List Form) (phi : Form) : Prop :=
  ∃ n, BProv B (chainB B L0 n) phi

private theorem Tinf_of_chain_in (B : Form → Prop) (L0 : List Form)
    (n : Nat) (phi : Form) (h : phi ∈ chainB B L0 n) : Tinf B L0 phi :=
  ⟨n, BProv_ass (by simpa using h)⟩

theorem BProv_weaken_chain (B : Form → Prop) (L0 : List Form) (n n' : Nat)
    (phi : Form) (hle : n ≤ n') (h : BProv B (chainB B L0 n) phi) :
    BProv B (chainB B L0 n') phi :=
  BProv_mono B _ _ phi (chainB_mono B L0 n' n hle) h

theorem BProv_mp (B : Form → Prop) (L : List Form) (a b : Form)
    (h1 : BProv B L (fImp a b)) (h2 : BProv B L a) : BProv B L b :=
  BProv_rule2 (fun Δ hImp ha => Prov.P_impE Δ a b hImp ha) h1 h2

/-! ### Natural-deduction rules lifted to relative provability

These rules are theory-independent.  They live beside `BProv`, rather than in
any particular interpretation, so every future relative theory can reuse the
same finite-axiom bookkeeping. -/

/-- A relative proof may ignore one extra finite-context assumption. -/
theorem BProv_context_cons {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G b) : BProv B (a :: G) b :=
  BProv_mono B G (a :: G) b
    (fun _ hx => List.mem_cons.mpr (Or.inr hx)) h

/-- Relative provability is closed under implication introduction. -/
theorem BProv_impI {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B (a :: G) b) : BProv B G (fImp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  grind

/-- Implication introduction behind a fixed prefix of assumptions. -/
theorem BProv_impI_after_prefix {B : Form → Prop} {Γ Δ : List Form}
    {a b : Form}
    (h : BProv B (Γ ++ a :: Δ) b) :
    BProv B (Γ ++ Δ) (fImp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  grind

/-- Relative provability is closed under conjunction introduction. -/
theorem BProv_andI {B : Form → Prop} {G : List Form} {a b : Form}
    (ha : BProv B G a) (hb : BProv B G b) : BProv B G (fAnd a b) :=
  BProv_rule2 (fun Δ ha' hb' => Prov.P_andI Δ a b ha' hb') ha hb

/-- Relative provability is closed under bottom elimination. -/
theorem BProv_botE {B : Form → Prop} {G : List Form} {a : Form}
    (hbot : BProv B G fBot) : BProv B G a :=
  BProv_rule1 (fun Δ hbot' => Prov.P_botE Δ a hbot') hbot

/-- Relative provability is closed under the first conjunction projection. -/
theorem BProv_andE1 {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fAnd a b)) : BProv B G a :=
  BProv_rule1 (fun Δ hand => Prov.P_andE1 Δ a b hand) h

/-- Relative provability is closed under the second conjunction projection. -/
theorem BProv_andE2 {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fAnd a b)) : BProv B G b :=
  BProv_rule1 (fun Δ hand => Prov.P_andE2 Δ a b hand) h

/-- Relative provability is closed under left disjunction introduction. -/
theorem BProv_orI1 {B : Form → Prop} {G : List Form} {a b : Form}
    (ha : BProv B G a) : BProv B G (fOr a b) :=
  BProv_rule1 (fun Δ ha' => Prov.P_orI1 Δ a b ha') ha

/-- Relative provability is closed under right disjunction introduction. -/
theorem BProv_orI2 {B : Form → Prop} {G : List Form} {a b : Form}
    (hb : BProv B G b) : BProv B G (fOr a b) :=
  BProv_rule1 (fun Δ hb' => Prov.P_orI2 Δ a b hb') hb

/-- Disjunction elimination when both branches are already implications in
the shared context. -/
theorem BProv_orE_imp {B : Form → Prop} {G : List Form} {a b c : Form}
    (hor : BProv B G (fOr a b))
    (ha : BProv B G (fImp a c))
    (hb : BProv B G (fImp b c)) : BProv B G c := by
  apply BProv_derive
    (Prov_orE_imp (G := [fOr a b, fImp a c, fImp b c])
      (a := a) (b := b) (c := c)
      (Prov.P_ass _ _ (by simp))
      (Prov.P_ass _ _ (by simp))
      (Prov.P_ass _ _ (by simp)))
  intro g hg
  simp at hg
  rcases hg with rfl | rfl | rfl
  · exact hor
  · exact ha
  · exact hb

/-- Relative provability is closed under disjunction elimination. -/
theorem BProv_orE {B : Form → Prop} {G : List Form} {a b c : Form}
    (hor : BProv B G (fOr a b))
    (ha : BProv B (a :: G) c)
    (hb : BProv B (b :: G) c) : BProv B G c :=
  BProv_orE_imp hor (BProv_impI ha) (BProv_impI hb)

/-- Disjunction elimination with a fixed prefix before each branch
assumption. -/
theorem BProv_orE_after_prefix {B : Form → Prop} {Γ Δ : List Form}
    {a b c : Form}
    (hor : BProv B (Γ ++ Δ) (fOr a b))
    (ha : BProv B (Γ ++ a :: Δ) c)
    (hb : BProv B (Γ ++ b :: Δ) c) :
    BProv B (Γ ++ Δ) c :=
  BProv_orE_imp hor
    (BProv_impI_after_prefix ha) (BProv_impI_after_prefix hb)

/-- Relative provability is closed under universal elimination. -/
theorem BProv_allE {B : Form → Prop} {G : List Form} {a : Form} {k : Nat}
    (h : BProv B G (fAll a)) : BProv B G (rename (inst k) a) :=
  BProv_rule1 (fun Δ hall => Prov.P_allE Δ a k hall) h

/-- Relative provability is closed under existential introduction. -/
theorem BProv_exI {B : Form → Prop} {G : List Form} {a : Form} {k : Nat}
    (h : BProv B G (rename (inst k) a)) : BProv B G (fEx a) :=
  BProv_rule1 (fun Δ hex => Prov.P_exI Δ a k hex) h

/-- A finite list of axioms from a sentence theory is unchanged by renaming. -/
theorem map_rename_eq_of_sentences {B : Form → Prop} (hB : Sentences B)
    {L : List Form} (hL : ∀ x, x ∈ L → B x) (r : Nat → Nat) :
    L.map (rename r) = L := by
  calc
    L.map (rename r) = L.map (fun x => x) := by
      apply List.map_congr_left
      intro x hx
      exact rename_eq_of_sentence x (hB x (hL x hx)) r
    _ = L := by simp

/-- Universal introduction for a relative proof whose theory axioms are
sentences. -/
theorem BProv_allI_of_sentences {B : Form → Prop} (hB : Sentences B)
    {G : List Form} {a : Form}
    (h : BProv B (G.map (rename Nat.succ)) a) : BProv B G (fAll a) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap := map_rename_eq_of_sentences hB hL Nat.succ
  refine ⟨L, hL, ?_⟩
  apply Prov.P_allI
  apply Prov_weaken hp
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Existential elimination for a relative proof whose theory axioms are
sentences. -/
theorem BProv_exE_of_sentences {B : Form → Prop} (hB : Sentences B)
    {G : List Form} {a c : Form}
    (hex : BProv B G (fEx a))
    (hbody : BProv B (a :: G.map (rename Nat.succ))
      (rename Nat.succ c)) : BProv B G c := by
  rcases hex with ⟨Le, hLe, hpe⟩
  rcases hbody with ⟨Lb, hLb, hpb⟩
  have hLbmap := map_rename_eq_of_sentences hB hLb Nat.succ
  refine ⟨Le ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_exE _ a c
    · apply Prov_weaken hpe
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · apply List.mem_cons.mpr
        apply Or.inr
        simp only [List.map_append, List.mem_append]
        apply Or.inl
        exact Or.inr (by simpa [hLbmap] using hx)
      · rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · apply List.mem_cons.mpr
          apply Or.inr
          simp only [List.map_append, List.mem_append]
          exact Or.inr hx

/-! ### Directed connective and equivalence calculus -/

/-- Implication is contravariant in its premise and covariant in its result. -/
theorem BProv_imp_mono {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fImp a' a))
    (hb : BProv B G (fImp b b')) :
    BProv B G (fImp (fImp a b) (fImp a' b')) := by
  apply BProv_impI
  apply BProv_impI
  let C : List Form := a' :: fImp a b :: G
  have ha'C : BProv B C a' := BProv_ass (by simp [C])
  have haC : BProv B C a :=
    BProv_mp B C a' a
      (BProv_context_cons (BProv_context_cons ha)) ha'C
  have habC : BProv B C (fImp a b) := BProv_ass (by simp [C])
  have hbC : BProv B C b := BProv_mp B C a b habC haC
  exact BProv_mp B C b b'
    (BProv_context_cons (BProv_context_cons hb)) hbC

/-- Conjunction is covariant in both components. -/
theorem BProv_and_mono {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fImp a a'))
    (hb : BProv B G (fImp b b')) :
    BProv B G (fImp (fAnd a b) (fAnd a' b')) := by
  apply BProv_impI
  let C : List Form := fAnd a b :: G
  have habC : BProv B C (fAnd a b) := BProv_ass (by simp [C])
  exact BProv_andI
    (BProv_mp B C a a' (BProv_context_cons ha) (BProv_andE1 habC))
    (BProv_mp B C b b' (BProv_context_cons hb) (BProv_andE2 habC))

/-- Disjunction is covariant in both components. -/
theorem BProv_or_mono {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fImp a a'))
    (hb : BProv B G (fImp b b')) :
    BProv B G (fImp (fOr a b) (fOr a' b')) := by
  apply BProv_impI
  let C : List Form := fOr a b :: G
  have horC : BProv B C (fOr a b) := BProv_ass (by simp [C])
  apply BProv_orE horC
  · exact BProv_orI1
      (BProv_mp B (a :: C) a a'
        (BProv_context_cons (BProv_context_cons ha))
        (BProv_ass (by simp)))
  · exact BProv_orI2
      (BProv_mp B (b :: C) b b'
        (BProv_context_cons (BProv_context_cons hb))
        (BProv_ass (by simp)))

/-- Build a formula equivalence from its two directed implications. -/
theorem BProv_fIff_intro {B : Form → Prop} {G : List Form} {a b : Form}
    (hab : BProv B G (fImp a b))
    (hba : BProv B G (fImp b a)) : BProv B G (fIff a b) := by
  simpa [fIff] using BProv_andI hab hba

theorem BProv_fIff_forward {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fIff a b)) : BProv B G (fImp a b) := by
  simpa [fIff] using BProv_andE1 h

theorem BProv_fIff_reverse {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fIff a b)) : BProv B G (fImp b a) := by
  simpa [fIff] using BProv_andE2 h

theorem BProv_fIff_refl {B : Form → Prop} {G : List Form} (a : Form) :
    BProv B G (fIff a a) := by
  have haa : BProv B G (fImp a a) :=
    BProv_impI (BProv_ass (by simp))
  exact BProv_fIff_intro haa haa

theorem BProv_fIff_imp_congr {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fImp a b) (fImp a' b')) :=
  BProv_fIff_intro
    (BProv_imp_mono (BProv_fIff_reverse ha) (BProv_fIff_forward hb))
    (BProv_imp_mono (BProv_fIff_forward ha) (BProv_fIff_reverse hb))

theorem BProv_fIff_and_congr {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fAnd a b) (fAnd a' b')) :=
  BProv_fIff_intro
    (BProv_and_mono (BProv_fIff_forward ha) (BProv_fIff_forward hb))
    (BProv_and_mono (BProv_fIff_reverse ha) (BProv_fIff_reverse hb))

theorem BProv_fIff_or_congr {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fOr a b) (fOr a' b')) :=
  BProv_fIff_intro
    (BProv_or_mono (BProv_fIff_forward ha) (BProv_fIff_forward hb))
    (BProv_or_mono (BProv_fIff_reverse ha) (BProv_fIff_reverse hb))

theorem stepB_pos_in (B : Form → Prop) (L : List Form) (phi : Form)
    (hc : BCon B (phi :: L)) : phi ∈ stepB B L phi := by
  unfold stepB
  rw [if_pos hc]
  cases phi <;> simp

theorem stepB_neg_in (B : Form → Prop) (L : List Form) (phi : Form)
    (hnc : ¬ BCon B (phi :: L)) : (fImp phi fBot) ∈ stepB B L phi := by
  unfold stepB
  rw [if_neg hnc]
  cases phi <;> simp

theorem stepB_ex_pos (B : Form → Prop) (L : List Form) (a : Form)
    (hc : BCon B (fEx a :: L)) :
    rename (inst (freshFor (fEx a :: L))) a ∈ stepB B L (fEx a) := by
  unfold stepB
  rw [if_pos hc]
  simp

theorem stepB_all_neg (B : Form → Prop) (L : List Form) (a : Form)
    (hnc : ¬ BCon B (fAll a :: L)) :
    fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
      ∈ stepB B L (fAll a) := by
  unfold stepB
  rw [if_neg hnc]
  simp

theorem Tinf_cons (B : Form → Prop) (L0 : List Form)
    (hB : Sentences B) (h0 : BCon B L0) : ¬ Tinf B L0 fBot :=
  fun ⟨n, hn⟩ => chainB_con B L0 hB h0 n hn

theorem Tinf_compl (B : Form → Prop) (L0 : List Form) (phi : Form) :
    Tinf B L0 phi ∨ Tinf B L0 (fImp phi fBot) := by
  obtain ⟨n, rfl⟩ := Enum_surj phi
  rcases stepB_decides B (chainB B L0 n) (Enum n) with hin | hin
  · exact Or.inl (Tinf_of_chain_in B L0 (n+1) (Enum n) (by simpa [chainB] using hin))
  · exact Or.inr (Tinf_of_chain_in B L0 (n+1) _ (by simpa [chainB] using hin))

private theorem Tinf_common_stage (B : Form → Prop) (L0 : List Form) :
    ∀ G : List Form, (∀ x ∈ G, Tinf B L0 x) →
      ∃ n, ∀ x ∈ G, BProv B (chainB B L0 n) x := by
  intro G
  induction G with
  | nil => intro _; exact ⟨0, fun x hx => nomatch hx⟩
  | cons g G' ih =>
    intro hall
    obtain ⟨ng, hg⟩ := hall g (by simp)
    obtain ⟨n, hn⟩ := ih (fun x hx => hall x (by simp [hx]))
    refine ⟨max ng n, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact BProv_weaken_chain B L0 ng (max ng n) x (by omega) hg
    · exact BProv_weaken_chain B L0 n (max ng n) x (by omega) (hn x hx)

theorem Tinf_bound (B : Form → Prop) (L0 : List Form) :
    ∀ G : List Form, (∀ x ∈ G, Tinf B L0 x) →
      ∃ n Gb, (∀ x ∈ Gb, B x) ∧
        (∀ x ∈ G, Prov (Gb ++ chainB B L0 n) x) := by
  intro G hall
  obtain ⟨n, hn⟩ := Tinf_common_stage B L0 G hall
  obtain ⟨Gb, hGb, hp⟩ := BProv_bound_list B (chainB B L0 n) G hn
  exact ⟨n, Gb, hGb, hp⟩

theorem Tinf_closed (B : Form → Prop) (L0 : List Form) (G : List Form)
    (phi : Form) (hall : ∀ x ∈ G, Tinf B L0 x) (hp : Prov G phi) :
    Tinf B L0 phi := by
  obtain ⟨N, Gb, hGb, hN⟩ := Tinf_bound B L0 G hall
  exact ⟨N, Gb, hGb, Prov_cut hp (Gb ++ chainB B L0 N) hN⟩

theorem Tinf_mp (B : Form → Prop) (L0 : List Form) (a b : Form)
    (hImp : Tinf B L0 (fImp a b)) (ha : Tinf B L0 a) : Tinf B L0 b := by
  apply Tinf_closed B L0 [fImp a b, a] b
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hImp
    · exact ha
  · exact Prov.P_impE _ a b
      (Prov.P_ass _ _ (by simp))
      (Prov.P_ass _ _ (by simp))

theorem Tinf_henkin_ex (B : Form → Prop) (L0 : List Form)
    (hB : Sentences B) (h0 : BCon B L0) (a : Form)
    (hex : Tinf B L0 (fEx a)) : ∃ k, Tinf B L0 (rename (inst k) a) := by
  obtain ⟨m, hm⟩ := Enum_surj (fEx a)
  rcases Classical.em (BCon B (fEx a :: chainB B L0 m)) with hpos | hnc
  · refine ⟨freshFor (fEx a :: chainB B L0 m), Tinf_of_chain_in B L0 (m+1) _ ?_⟩
    simpa [chainB, hm] using stepB_ex_pos B (chainB B L0 m) a hpos
  · exfalso
    have hneg : Tinf B L0 (fImp (fEx a) fBot) := by
      apply Tinf_of_chain_in B L0 (m+1)
      simpa [chainB, hm] using stepB_neg_in B (chainB B L0 m) (fEx a) hnc
    exact (Tinf_cons B L0 hB h0) (Tinf_mp B L0 (fEx a) fBot hneg hex)

theorem Tinf_henkin_all (B : Form → Prop) (L0 : List Form)
    (hB : Sentences B) (h0 : BCon B L0) (a : Form)
    (hall : ∀ k, Tinf B L0 (rename (inst k) a)) : Tinf B L0 (fAll a) := by
  rcases Tinf_compl B L0 (fAll a) with hpos | hneg
  · exact hpos
  exfalso
  obtain ⟨m, hm⟩ := Enum_surj (fAll a)
  rcases Classical.em (BCon B (fAll a :: chainB B L0 m)) with hc | hnc
  · have hposfa : Tinf B L0 (fAll a) := by
      apply Tinf_of_chain_in B L0 (m+1)
      simpa [chainB, hm] using stepB_pos_in B (chainB B L0 m) (fAll a) hc
    exact (Tinf_cons B L0 hB h0) (Tinf_mp B L0 (fAll a) fBot hneg hposfa)
  · have hnegw : Tinf B L0
        (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: chainB B L0 m))) a)
              fBot) := by
      apply Tinf_of_chain_in B L0 (m+1)
      simpa [chainB, hm] using stepB_all_neg B (chainB B L0 m) a hnc
    exact (Tinf_cons B L0 hB h0)
      (Tinf_mp B L0
        (rename (inst (freshFor (fImp (fAll a) fBot :: chainB B L0 m))) a)
        fBot hnegw
        (hall (freshFor (fImp (fAll a) fBot :: chainB B L0 m))))

/-- MODEL EXISTENCE for a consistent sentence theory with a finite extra list. -/
theorem model_of_BCon (B : Form → Prop) (L0 : List Form)
    (hB : Sentences B) (h0 : BCon B L0) :
    ∃ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B g → Sat m v g) ∧ (∀ g ∈ L0, Sat m v g) := by
  obtain ⟨Dom, m, v, hsat⟩ := model_exists (Tinf B L0)
    ⟨Tinf_cons B L0 hB h0, Tinf_compl B L0, Tinf_closed B L0,
     Tinf_henkin_ex B L0 hB h0, Tinf_henkin_all B L0 hB h0⟩
  refine ⟨Dom, m, v, ?_, ?_⟩
  · intro g hg
    apply (hsat g).mpr
    exact ⟨0, BProv_ax hg⟩
  · intro g hg
    exact (hsat g).mpr (Tinf_of_chain_in B L0 0 g (by simpa [chainB] using hg))

/-! ## Finite-context completeness, as the `B = ∅` instance -/

/-- Provability from the empty base theory is plain provability. -/
theorem BProv_empty (G : List Form) (phi : Form) :
    BProv (fun _ => False) G phi ↔ Prov G phi := by
  constructor
  · intro ⟨Gb, hGb, hp⟩
    match Gb, hp with
    | [], hp => exact hp
    | x :: _, _ => exact (hGb x (by simp)).elim
  · exact BProv_of_Prov

/-- Every consistent finite context has a model (the `B = ∅` instance of
`model_of_BCon`). -/
theorem model_of_con (G0 : List Form) (hG0 : Con G0) :
    ∃ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      ∀ g ∈ G0, Sat m v g := by
  obtain ⟨Dom, m, v, _, hsatL⟩ :=
    model_of_BCon (fun _ => False) G0 (fun _ hf => hf.elim)
      (fun hbad => hG0 ((BProv_empty G0 fBot).mp hbad))
  exact ⟨Dom, m, v, hsatL⟩

/-- Shared countermodel kernel for finite and sentence-theory completeness. -/
private theorem completeness_inf_context_core (B : Form → Prop)
    (G : List Form) (psi : Form) (hB : Sentences B)
    (hval : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B g → Sat m v g) →
      (∀ g, g ∈ G → Sat m v g) →
      Sat m v psi) :
    BProv B G psi := by
  apply Classical.byContradiction
  intro hnp
  have hBcon : BCon B (fImp psi fBot :: G) := by
    intro ⟨Gb, hGb, hbad⟩
    apply hnp
    refine ⟨Gb, hGb, ?_⟩
    apply Prov_byContra
    exact Prov_exch (G := Gb ++ (fImp psi fBot :: G)) (by mem_tac) hbad
  obtain ⟨Dom, m, v, hsatB, hsatL⟩ :=
    model_of_BCon B (fImp psi fBot :: G) hB hBcon
  exact (hsatL (fImp psi fBot) (by simp))
    (hval Dom m v hsatB (fun g hg => hsatL g (by simp [hg])))

/-- COMPLETENESS: validity in all models implies provability. -/
theorem completeness (G : List Form) (phi : Form)
    (hval : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g ∈ G, Sat m v g) → Sat m v phi) :
    Prov G phi := by
  apply (BProv_empty G phi).mp
  exact completeness_inf_context_core (fun _ => False) G phi
    (fun _ hf => hf.elim) (fun Dom m v _ hG => hval Dom m v hG)

/-- SOUNDNESS + COMPLETENESS: provability coincides with validity. -/
theorem prov_iff_valid (G : List Form) (phi : Form) :
    Prov G phi ↔
      ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
        (∀ g ∈ G, Sat m v g) → Sat m v phi := by
  constructor
  · intro h Dom m v hg
    exact soundness h v hg
  · exact completeness G phi

/-- Relative completeness with a finite context: semantic validity over every
model of the sentence theory `B` satisfying the finite list `G` yields
relative provability from `B` and `G`.  Only `B` must consist of sentences;
neither the finite context nor the target formula has that restriction. -/
theorem completeness_inf_context (B : Form → Prop) (G : List Form) (psi : Form)
    (hB : Sentences B)
    (hval : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B g → Sat m v g) →
      (∀ g, g ∈ G → Sat m v g) →
      Sat m v psi) :
    BProv B G psi :=
  completeness_inf_context_core B G psi hB hval

/-- INFINITE COMPLETENESS: the historical empty-context interface.
The target-sentence premise is retained for compatibility; the stronger
finite-context theorem does not need it. -/
theorem completeness_inf (B : Form → Prop) (psi : Form)
    (hB : Sentences B) (_hpsi : Sentence psi)
    (hval : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B g → Sat m v g) → Sat m v psi) :
    BProv B [] psi :=
  completeness_inf_context B [] psi hB
    (fun Dom m v hsatB _ => hval Dom m v hsatB)

/-- SEMANTIC THEORY TRANSFER: if every model of `B₂` is a model of `B₁`,
proofs over `B₁` transfer to `B₂`.  The finite context and target formula are
unrestricted; only the destination base theory must consist of sentences. -/
theorem theory_transfer (B₁ B₂ : Form → Prop) (G : List Form) (psi : Form)
    (hB₂ : Sentences B₂)
    (hmodels : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B₂ g → Sat m v g) → ∀ g, B₁ g → Sat m v g)
    (hp : BProv B₁ G psi) : BProv B₂ G psi :=
  completeness_inf_context B₂ G psi hB₂ fun Dom m v hB₂sat hGsat =>
    soundness_BProv hp v (hmodels Dom m v hB₂sat) hGsat

/-- DEDUCTIVE EQUIVALENCE: two sentence theories with the same models prove
the same sentences. -/
theorem theory_equiv (B1 B2 : Form → Prop)
    (hB1 : Sentences B1) (hB2 : Sentences B2)
    (hsame : ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      (∀ g, B1 g → Sat m v g) ↔ (∀ g, B2 g → Sat m v g))
    (psi : Form) (_hpsi : Sentence psi) :
    BProv B1 [] psi ↔ BProv B2 [] psi := by
  constructor
  · exact theory_transfer B1 B2 [] psi hB2
      (fun Dom m v hB2sat => (hsame Dom m v).mpr hB2sat)
  · exact theory_transfer B2 B1 [] psi hB1
      (fun Dom m v hB1sat => (hsame Dom m v).mp hB1sat)

end SetTheory
