/-
  Zf.lean

  FIRST-ORDER ZF, independent of the Closure axiomatization T:

   - the ZF axioms as formulas (Ext_form … Reg_form, with the Separation
     and Replacement schemas over `Form`), the axiom set `ZFax` and
     provability `ZFprov`, and the SENTENCE theory `ZFax_s` (every axiom
     universally closed by `sealF`);
   - extraction bridges: satisfaction of each (open) axiom formula in a
     structure (V, mem) is equivalent to the abstract semantic axiom
     (`bridge_Ext` … `bridge_Repl`, with legacy `_fwd` projections);
   - INTERNAL MATHEMATICS of an arbitrary first-order model of
     {Ext, Sep, Pair, Union, Inf, Repl} (note: no Powerset, no
     Regularity): internal set algebra, Kuratowski pairs with
     injectivity, an internal omega with the definable-induction schema
     `omega_ind`, a formula-macro library with satisfaction specs, and
     the FINITE RECURSION THEOREM (approximations `Approx`, existence +
     agreement, functional stage relation `Theta`), giving

       ClosureFO_of_ZF : every definable set-like relation admits a
       closure superset of any seed — inside every such model.

  Lean 4 port of the Rocq/Coq development `SetTheory/ZF/Coq/Zf.v`.

  De Bruijn convention note: where the Coq file writes an offset lookup
  `off + k`, this port writes `k + off` (and `S i` becomes `i + 1`), so
  that Lean's `Nat.add` — which recurses on its SECOND argument — reduces
  the environment lookups definitionally, exactly as Coq's `plus` (which
  recurses on the first) did there.
-/
import FirstOrder.Calculus

namespace SetTheory

open Form

/-! ## Renamings used to place a schema's formula under fresh binders -/

def rsep : Nat → Nat
  | 0 => 0
  | i+1 => i + 3

def rf1 : Nat → Nat
  | 0 => 1
  | 1 => 2
  | j+2 => j + 3

def rf2 : Nat → Nat
  | 0 => 0
  | 1 => 2
  | j+2 => j + 3

def ri : Nat → Nat
  | 0 => 1
  | 1 => 0
  | j+2 => j + 4

/-! ### Environment lemmas for the schema renamings -/

section EnvLemmas

universe u
variable {V : Type u}

theorem rsep_env (dx s da : V) (e : Nat → V) :
    ∀ n, scons dx (scons s (scons da e)) (rsep n) = scons dx e n := by
  intro n
  match n with
  | 0 => rfl
  | i+1 => rfl

theorem rf1_env (y2 y1 x : V) (e : Nat → V) :
    ∀ n, scons y2 (scons y1 (scons x e)) (rf1 n) = scons y1 (scons x e) n := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

theorem rf2_env (y2 y1 x : V) (e : Nat → V) :
    ∀ n, scons y2 (scons y1 (scons x e)) (rf2 n) = scons y2 (scons x e) n := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

theorem ri_env (x y r a : V) (e : Nat → V) :
    ∀ n, scons x (scons y (scons r (scons a e))) (ri n) = scons y (scons x e) n := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

end EnvLemmas

/-! ## The ZF axioms as closed formulas -/

def Ext_form : Form :=
  fAll (fAll (fImp (fAll (fIff (fMem 0 2) (fMem 0 1))) (fEq 1 0)))
def Pair_form : Form :=
  fAll (fAll (fEx (fAll (fIff (fMem 0 1) (fOr (fEq 0 3) (fEq 0 2))))))
def Union_form : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fEx (fAnd (fMem 1 0) (fMem 0 3))))))
def Pow_form : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 3))))))
def Inf_form : Form :=
  fEx (fAnd
        (fEx (fAnd (fMem 0 1) (fAll (fImp (fMem 0 1) fBot))))
        (fAll (fImp (fMem 0 1)
                 (fEx (fAnd (fMem 0 2)
                         (fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2)))))))))
def Reg_form : Form :=
  fAll (fImp (fEx (fMem 0 1))
          (fEx (fAnd (fMem 0 1)
                  (fImp (fEx (fAnd (fMem 0 1) (fMem 0 2))) fBot))))
def Sep_form (phi : Form) : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fAnd (fMem 0 2) (rename rsep phi)))))
def Func_form (psi : Form) : Form :=
  fAll (fAll (fAll (fImp (fAnd (rename rf1 psi) (rename rf2 psi)) (fEq 1 0))))
def Image_form (psi : Form) : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fEx (fAnd (fMem 0 3) (rename ri psi))))))
def Repl_form (psi : Form) : Form := fImp (Func_form psi) (Image_form psi)

/-! ## The ZF axiom set: list-context provability, and as a sentence theory -/

def ZFax (f : Form) : Prop :=
  f = Ext_form ∨ f = Pair_form ∨ f = Union_form ∨ f = Pow_form ∨
  f = Inf_form ∨ f = Reg_form ∨
  (∃ phi, f = Sep_form phi) ∨ (∃ psi, f = Repl_form psi)

def ZFprov (phi : Form) : Prop :=
  ∃ G, (∀ x ∈ G, ZFax x) ∧ Prov G phi

def ZFax_s (f : Form) : Prop :=
  f = sealF Ext_form ∨ f = sealF Reg_form ∨ f = sealF Pow_form ∨
  f = sealF Pair_form ∨ f = sealF Union_form ∨ f = sealF Inf_form ∨
  (∃ phi, f = sealF (Sep_form phi)) ∨ (∃ psi, f = sealF (Repl_form psi))

theorem Sentences_ZF : Sentences ZFax_s := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩ <;>
    exact Sentence_seal _

/-! ## Extraction bridges: open-axiom satisfaction ↔ semantic axioms -/

section Bridges

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem bridge_Ext :
    (∀ e : Nat → V, Sat mem e Ext_form) ↔
      ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b := by
  constructor
  · intro h a b hab
    exact h (fun _ => a) a b (fun x => ⟨(hab x).mp, (hab x).mpr⟩)
  · intro h e a b hab
    exact h a b (fun x => ⟨(hab x).1, (hab x).2⟩)

theorem bridge_Ext_fwd (H : ∀ e : Nat → V, Sat mem e Ext_form) :
    ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b :=
  bridge_Ext.mp H

theorem bridge_Pow :
    (∀ e : Nat → V, Sat mem e Pow_form) ↔
      ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a := by
  constructor
  · intro h a
    obtain ⟨p, hp⟩ := h (fun _ => a) a
    exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩
  · intro h e a
    obtain ⟨p, hp⟩ := h a
    exact ⟨p, fun x => ⟨(hp x).mp, (hp x).mpr⟩⟩

theorem bridge_Pow_fwd (H : ∀ e : Nat → V, Sat mem e Pow_form) :
    ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a :=
  bridge_Pow.mp H

theorem bridge_Reg :
    (∀ e : Nat → V, Sat mem e Reg_form) ↔
      ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a := by
  constructor
  · intro h a hne
    exact h (fun _ => a) a hne
  · intro h e a hne
    exact h a hne

theorem bridge_Reg_fwd (H : ∀ e : Nat → V, Sat mem e Reg_form) :
    ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a :=
  bridge_Reg.mp H

theorem rsep_rel (phi : Form) (x s da : V) (e : Nat → V) :
    Sat mem (scons x (scons s (scons da e))) (rename rsep phi)
      ↔ Sat mem (scons x e) phi := by
  exact Sat_rename_ext phi rsep _ _ (rsep_env x s da e)

theorem bridge_Sep :
    (∀ (phi : Form) (e : Nat → V), Sat mem e (Sep_form phi)) ↔
      ∀ (phi : Form) (e : Nat → V) (a : V),
        ∃ s, ∀ x, mem x s ↔ (mem x a ∧ Sat mem (scons x e) phi) := by
  have hbody (phi : Form) (e : Nat → V) (a s x : V) :
      (mem x a ∧ Sat mem (scons x (scons s (scons a e))) (rename rsep phi)) ↔
        (mem x a ∧ Sat mem (scons x e) phi) :=
    and_congr_right fun _ => rsep_rel phi x s a e
  constructor
  · intro h phi e a
    obtain ⟨s, hs⟩ := h phi e a
    exact ⟨s, fun x =>
      ((Sat_fIff (mem := mem)).mp (hs x)).trans (hbody phi e a s x)⟩
  · intro h phi e a
    obtain ⟨s, hs⟩ := h phi e a
    exact ⟨s, fun x => (Sat_fIff (mem := mem)).mpr
      ((hs x).trans (hbody phi e a s x).symm)⟩

theorem bridge_Sep_fwd (H : ∀ (phi : Form) (e : Nat → V), Sat mem e (Sep_form phi)) :
    ∀ (phi : Form) (e : Nat → V) (a : V),
      ∃ s, ∀ x, mem x s ↔ (mem x a ∧ Sat mem (scons x e) phi) :=
  bridge_Sep.mp H

/-! ### Bridges for the four generative axioms -/

theorem bridge_Pair :
    (∀ e : Nat → V, Sat mem e Pair_form) ↔
      ∀ a b, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b) := by
  simp only [Pair_form, Sat, Sat_fIff, scons]
  constructor
  · intro h a b
    simpa only using h (fun _ => a) a b
  · intro h e a b
    simpa only using h a b

theorem bridge_Pair_fwd (H : ∀ e : Nat → V, Sat mem e Pair_form) :
    ∀ a b, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b) :=
  bridge_Pair.mp H

theorem bridge_Union :
    (∀ e : Nat → V, Sat mem e Union_form) ↔
      ∀ u, ∃ w, ∀ x, mem x w ↔ ∃ v, mem x v ∧ mem v u := by
  simp only [Union_form, Sat, Sat_fIff, scons]
  constructor
  · intro h u
    simpa only using h (fun _ => u) u
  · intro h e u
    simpa only using h u

theorem bridge_Union_fwd (H : ∀ e : Nat → V, Sat mem e Union_form) :
    ∀ u, ∃ w, ∀ x, mem x w ↔ ∃ v, mem x v ∧ mem v u :=
  bridge_Union.mp H

/-- `Inf_form` is closed, but its pointwise environment stays explicit so the
legacy extraction theorem is a literal projection. -/
theorem bridge_Inf (v : Nat → V) :
    Sat mem v Inf_form ↔
      ∃ I, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
        (∀ x, mem x I →
          ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) := by
  simp only [Inf_form, Sat, Sat_fIff, scons]

theorem bridge_Inf_fwd (v : Nat → V) (H : Sat mem v Inf_form) :
    ∃ I, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
      (∀ x, mem x I →
        ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) :=
  (bridge_Inf v).mp H

/-- The internal functionality formula says exactly that `psi` defines a
functional relation under the surrounding parameter environment. -/
theorem bridge_Func (psi : Form) (e : Nat → V) :
    Sat mem e (Func_form psi) ↔ Functional (relOf mem psi e) := by
  constructor
  · intro h x y1 y2 h1 h2
    exact h x y1 y2 ⟨
      (Sat_rename_relOf psi rf1 _ e y1 x (rf1_env y2 y1 x e)).mpr h1,
      (Sat_rename_relOf psi rf2 _ e y2 x (rf2_env y2 y1 x e)).mpr h2⟩
  · intro h x y1 y2 hsat
    exact h x y1 y2
      ((Sat_rename_relOf psi rf1 _ e y1 x (rf1_env y2 y1 x e)).mp hsat.1)
      ((Sat_rename_relOf psi rf2 _ e y2 x (rf2_env y2 y1 x e)).mp hsat.2)

/-- The internal image formula denotes the set-theoretic image of `a` under
the relation defined by `psi`. -/
theorem bridge_Image (psi : Form) (e : Nat → V) :
    Sat mem e (Image_form psi) ↔
      ∀ a, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi e y x := by
  have hbody (a r y : V) :
      (∃ x, mem x a ∧
        Sat mem (scons x (scons y (scons r (scons a e)))) (rename ri psi)) ↔
      (∃ x, mem x a ∧ relOf mem psi e y x) := by
    apply exists_congr
    intro x
    exact and_congr_right fun _ =>
      Sat_rename_relOf psi ri _ e y x (ri_env x y r a e)
  constructor
  · intro h a
    obtain ⟨r, hr⟩ := h a
    exact ⟨r, fun y =>
      ((Sat_fIff (mem := mem)).mp (hr y)).trans (hbody a r y)⟩
  · intro h a
    obtain ⟨r, hr⟩ := h a
    exact ⟨r, fun y => (Sat_fIff (mem := mem)).mpr
      ((hr y).trans (hbody a r y).symm)⟩

/-- Satisfaction of a Replacement instance is exactly the semantic
replacement implication for the relation defined by `psi`. -/
theorem bridge_Repl (psi : Form) (e : Nat → V) :
    Sat mem e (Repl_form psi) ↔
      (Functional (relOf mem psi e) →
        ∀ a, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi e y x) := by
  constructor
  · intro h hfun
    exact (bridge_Image psi e).mp (h ((bridge_Func psi e).mpr hfun))
  · intro h hfunc
    exact (bridge_Image psi e).mpr (h ((bridge_Func psi e).mp hfunc))

theorem bridge_Repl_fwd (H : ∀ (psi : Form) (e : Nat → V), Sat mem e (Repl_form psi)) :
    ∀ (psi : Form) (e : Nat → V),
      Functional (relOf mem psi e) →
      ∀ a, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi e y x := by
  intro psi e
  exact (bridge_Repl psi e).mp (H psi e)

end Bridges

/-! ## Inside an arbitrary first-order ZF model (no Powerset, no Regularity):
the internal finite recursion theorem, and closure of any seed under any
definable set-like relation. -/

/-- The model-side ZF axioms (no Powerset, no Regularity), bundled.
(Coq renders these as six separate Section hypotheses `AxExt` … `AxRepl`;
the bundle contains exactly those six, so the "neither Powerset nor
Regularity is needed" sharpening stays visible in this definition.) -/
structure ZFAxioms {V : Type u} (mem : V → V → Prop) : Prop where
  ext : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  sep : ∀ (phi : Form) (e : Nat → V) (a : V),
    ∃ s, ∀ x, mem x s ↔ (mem x a ∧ Sat mem (scons x e) phi)
  pair : ∀ a b, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b)
  union : ∀ u, ∃ w, ∀ x, mem x w ↔ ∃ v, mem x v ∧ mem v u
  inf : ∃ I, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
    (∀ x, mem x I → ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x))
  repl : ∀ (psi : Form) (e : Nat → V), Functional (relOf mem psi e) →
    ∀ a, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi e y x

section ZfModel

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ### Internal set operators -/

noncomputable def sepD (H : ZFAxioms mem) (phi : Form) (e : Nat → V) (a : V) : V :=
  (H.sep phi e a).choose

theorem sepD_spec (H : ZFAxioms mem) (phi : Form) (e : Nat → V) (a x : V) :
    mem x (sepD H phi e a) ↔ (mem x a ∧ Sat mem (scons x e) phi) :=
  (H.sep phi e a).choose_spec x

noncomputable def vpair (H : ZFAxioms mem) (a b : V) : V := (H.pair a b).choose

theorem vpair_spec (H : ZFAxioms mem) (a b x : V) :
    mem x (vpair H a b) ↔ (x = a ∨ x = b) :=
  (H.pair a b).choose_spec x

noncomputable def vsingle (H : ZFAxioms mem) (a : V) : V := vpair H a a

theorem vsingle_spec (H : ZFAxioms mem) (a x : V) :
    mem x (vsingle H a) ↔ x = a := by
  unfold vsingle
  rw [vpair_spec H a a x]
  grind

noncomputable def vunion (H : ZFAxioms mem) (u : V) : V := (H.union u).choose

theorem vunion_spec (H : ZFAxioms mem) (u x : V) :
    mem x (vunion H u) ↔ ∃ v, mem x v ∧ mem v u :=
  (H.union u).choose_spec x

noncomputable def vcup (H : ZFAxioms mem) (a b : V) : V := vunion H (vpair H a b)

theorem vcup_spec (H : ZFAxioms mem) (a b x : V) :
    mem x (vcup H a b) ↔ (mem x a ∨ mem x b) := by
  unfold vcup
  rw [vunion_spec H (vpair H a b) x]
  constructor
  · intro ⟨v, hxv, hv⟩
    rcases (vpair_spec H a b v).mp hv with rfl | rfl
    · exact Or.inl hxv
    · exact Or.inr hxv
  · intro h
    rcases h with ha | hb
    · exact ⟨a, ha, (vpair_spec H a b a).mpr (Or.inl rfl)⟩
    · exact ⟨b, hb, (vpair_spec H a b b).mpr (Or.inr rfl)⟩

noncomputable def vsucc (H : ZFAxioms mem) (a : V) : V := vcup H a (vsingle H a)

theorem vsucc_spec (H : ZFAxioms mem) (a x : V) :
    mem x (vsucc H a) ↔ (mem x a ∨ x = a) := by
  unfold vsucc
  rw [vcup_spec H a (vsingle H a) x, vsingle_spec H a x]

theorem vsucc_self (H : ZFAxioms mem) (a : V) : mem a (vsucc H a) :=
  (vsucc_spec H a a).mpr (Or.inr rfl)

noncomputable def InfSet (H : ZFAxioms mem) : V := H.inf.choose

theorem InfSet_spec (H : ZFAxioms mem) :
    (∃ e0, mem e0 (InfSet H) ∧ ∀ z, ¬ mem z e0) ∧
    (∀ x, mem x (InfSet H) →
      ∃ sx, mem sx (InfSet H) ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) :=
  H.inf.choose_spec

noncomputable def vempty (H : ZFAxioms mem) : V :=
  sepD H fBot (fun _ => InfSet H) (InfSet H)

theorem vempty_spec (H : ZFAxioms mem) (x : V) : ¬ mem x (vempty H) := by
  intro hx
  have h := (sepD_spec H fBot (fun _ => InfSet H) (InfSet H) x).mp hx
  exact h.2

theorem empty_in_InfSet (H : ZFAxioms mem) : mem (vempty H) (InfSet H) := by
  obtain ⟨⟨e0, he0, hemp⟩, _⟩ := InfSet_spec H
  have : e0 = vempty H := by
    apply H.ext
    intro t
    constructor
    · intro ht; exact absurd ht (hemp t)
    · intro ht; exact absurd ht (vempty_spec H t)
  rwa [this] at he0

theorem vsucc_in_InfSet (H : ZFAxioms mem) (x : V) (hx : mem x (InfSet H)) :
    mem (vsucc H x) (InfSet H) := by
  obtain ⟨_, hsucc⟩ := InfSet_spec H
  obtain ⟨sx, hsx, hspec⟩ := hsucc x hx
  have : sx = vsucc H x := by
    apply H.ext
    intro t
    rw [vsucc_spec H x t]
    exact ⟨(hspec t).1, (hspec t).2⟩
  rwa [this] at hsx

/-! ### Kuratowski pairs and injectivity -/

noncomputable def kpair (H : ZFAxioms mem) (a b : V) : V :=
  vpair H (vsingle H a) (vpair H a b)

theorem kpair_mem (H : ZFAxioms mem) (a b q : V) :
    mem q (kpair H a b) ↔ (q = vsingle H a ∨ q = vpair H a b) :=
  vpair_spec H _ _ q

theorem vsingle_inj (H : ZFAxioms mem) (a b : V)
    (h : vsingle H a = vsingle H b) : a = b := by
  have ha : mem a (vsingle H a) := (vsingle_spec H a a).mpr rfl
  rw [h] at ha
  exact (vsingle_spec H b a).mp ha

theorem vpair_single (H : ZFAxioms mem) (a b c : V)
    (h : vpair H a b = vsingle H c) : a = c ∧ b = c := by
  constructor
  · have ha : mem a (vpair H a b) := (vpair_spec H a b a).mpr (Or.inl rfl)
    rw [h] at ha
    exact (vsingle_spec H c a).mp ha
  · have hb : mem b (vpair H a b) := (vpair_spec H a b b).mpr (Or.inr rfl)
    rw [h] at hb
    exact (vsingle_spec H c b).mp hb

theorem kpair_inj (H : ZFAxioms mem) (a b c d : V)
    (h : kpair H a b = kpair H c d) : a = c ∧ b = d := by
  have hac : a = c := by
    have hs : mem (vsingle H a) (kpair H a b) :=
      (kpair_mem H a b _).mpr (Or.inl rfl)
    rw [h] at hs
    rcases (kpair_mem H c d _).mp hs with hs | hs
    · exact vsingle_inj H a c hs
    · exact ((vpair_single H c d a hs.symm).1).symm
  refine ⟨hac, ?_⟩
  subst hac
  -- h : kpair a b = kpair a d
  have h1 : mem (vpair H a b) (kpair H a b) :=
    (kpair_mem H a b _).mpr (Or.inr rfl)
  rw [h] at h1
  rcases (kpair_mem H a d _).mp h1 with h1 | h1
  · -- vpair a b = vsingle a, so b = a
    have hba : b = a := (vpair_single H a b a h1).2
    have h2 : mem (vpair H a d) (kpair H a d) :=
      (kpair_mem H a d _).mpr (Or.inr rfl)
    rw [← h] at h2
    rcases (kpair_mem H a b _).mp h2 with h2 | h2
    · have hda : d = a := (vpair_single H a d a h2).2
      rw [hba, hda]
    · have hd : mem d (vpair H a d) := (vpair_spec H a d d).mpr (Or.inr rfl)
      rw [h2] at hd
      rcases (vpair_spec H a b d).mp hd with hd | hd
      · rw [hba, hd]
      · exact hd.symm
  · -- vpair a b = vpair a d
    have hb : mem b (vpair H a b) := (vpair_spec H a b b).mpr (Or.inr rfl)
    rw [h1] at hb
    rcases (vpair_spec H a d b).mp hb with hb | hb
    · -- b = a
      have hd : mem d (vpair H a d) := (vpair_spec H a d d).mpr (Or.inr rfl)
      rw [← h1] at hd
      rcases (vpair_spec H a b d).mp hd with hd | hd
      · rw [hb, hd]
      · exact hd.symm
    · exact hb

/-! ### Formula macros with satisfaction specs

Each macro is a genuine `Form`; its spec lemma says exactly what its
satisfaction means.  Arguments are ABSOLUTE de Bruijn slots in the
environment at the use site; under an extra binder every slot shifts by
one, which the call sites account for explicitly.  (Coq marks each macro
`Local Opaque` after its spec; in Lean, `simp only [Sat]` leaves plain
`def`s folded automatically.) -/

/-- "slot `i` is the empty set" -/
def fEmptyF (i : Nat) : Form := fAll (fImp (fMem 0 (i+1)) fBot)

theorem fEmptyF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fEmptyF i) ↔ ee i = vempty H := by
  show (∀ d, mem d (ee i) → False) ↔ _
  constructor
  · intro h
    apply H.ext
    intro x
    constructor
    · intro hx; exact (h x hx).elim
    · intro hx; exact (vempty_spec H x hx).elim
  · intro heq d hd
    rw [heq] at hd
    exact vempty_spec H d hd

/-- `fSetByF i phi` says that slot `i` contains exactly the objects
satisfying `phi` under the newly bound slot 0. -/
def fSetByF (i : Nat) (phi : Form) : Form :=
  fAll (fIff (fMem 0 (i+1)) phi)

theorem fSetByF_sat (ee : Nat → V) (i : Nat) (phi : Form) :
    Sat mem ee (fSetByF i phi) ↔
      ∀ x, mem x (ee i) ↔ Sat mem (scons x ee) phi := by
  simp only [fSetByF, Sat, Sat_fIff, scons]

/-- Extensionality turns a semantic specification of the element formula
into the equality asserted by `fSetByF`. -/
theorem fSetByF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat)
    (phi : Form) (b : V)
    (hphi : ∀ x, Sat mem (scons x ee) phi ↔ mem x b) :
    Sat mem ee (fSetByF i phi) ↔ ee i = b := by
  rw [fSetByF_sat]
  constructor
  · intro h
    apply H.ext
    intro x
    exact (h x).trans (hphi x)
  · intro heq x
    rw [heq]
    exact (hphi x).symm

/-- "slot `i` = {slot `j`}" -/
def fSingF (i j : Nat) : Form :=
  fSetByF i (fEq 0 (j+1))

theorem fSingF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j : Nat) :
    Sat mem ee (fSingF i j) ↔ ee i = vsingle H (ee j) := by
  apply fSetByF_spec H
  intro x
  exact (vsingle_spec H (ee j) x).symm

/-- "slot `i` = {slot `j`, slot `k`}" -/
def fUPairF (i j k : Nat) : Form :=
  fSetByF i (fOr (fEq 0 (j+1)) (fEq 0 (k+1)))

theorem fUPairF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fUPairF i j k) ↔ ee i = vpair H (ee j) (ee k) := by
  apply fSetByF_spec H
  intro x
  exact (vpair_spec H (ee j) (ee k) x).symm

/-- "slot `i` = ⟨slot `j`, slot `k`⟩" (Kuratowski) -/
def fKPairF (i j k : Nat) : Form :=
  fSetByF i (fOr (fSingF 0 (j+1)) (fUPairF 0 (j+1) (k+1)))

theorem fKPairF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fKPairF i j k) ↔ ee i = kpair H (ee j) (ee k) := by
  apply fSetByF_spec H
  intro q
  change (Sat mem (scons q ee) (fSingF 0 (j+1)) ∨
      Sat mem (scons q ee) (fUPairF 0 (j+1) (k+1))) ↔ _
  rw [fSingF_spec H (scons q ee) 0 (j+1),
      fUPairF_spec H (scons q ee) 0 (j+1) (k+1),
      kpair_mem H (ee j) (ee k) q]
  simp only [scons]

/-- "⟨slot `i`, slot `j`⟩ ∈ slot `k`" -/
def fPairMemF (i j k : Nat) : Form :=
  fEx (fAnd (fKPairF 0 (i+1) (j+1)) (fMem 0 (k+1)))

theorem fPairMemF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fPairMemF i j k) ↔ mem (kpair H (ee i) (ee j)) (ee k) := by
  constructor
  · intro ⟨d, hd, hmem⟩
    have hd' : d = kpair H (ee i) (ee j) :=
      (fKPairF_spec H (scons d ee) 0 (i+1) (j+1)).mp hd
    have hmem' : mem d (ee k) := hmem
    rwa [hd'] at hmem'
  · intro h
    refine ⟨kpair H (ee i) (ee j), ?_, ?_⟩
    · exact (fKPairF_spec H (scons (kpair H (ee i) (ee j)) ee) 0 (i+1) (j+1)).mpr rfl
    · exact h

/-- "slot `i` = successor of slot `j`" -/
def fSuccF (i j : Nat) : Form :=
  fSetByF i (fOr (fMem 0 (j+1)) (fEq 0 (j+1)))

theorem fSuccF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j : Nat) :
    Sat mem ee (fSuccF i j) ↔ ee i = vsucc H (ee j) := by
  apply fSetByF_spec H
  intro x
  exact (vsucc_spec H (ee j) x).symm

/-! ### The internal omega -/

def inductiveV (H : ZFAxioms mem) (c : V) : Prop :=
  mem (vempty H) c ∧ ∀ y, mem y c → mem (vsucc H y) c

/-- "slot `i` is an inductive set" -/
def fInd (i : Nat) : Form :=
  fAnd (fEx (fAnd (fEmptyF 0) (fMem 0 (i+1))))
       (fAll (fImp (fMem 0 (i+1)) (fEx (fAnd (fSuccF 0 1) (fMem 0 (i+2))))))

theorem fInd_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fInd i) ↔ inductiveV H (ee i) := by
  constructor
  · intro ⟨⟨z, hz, hzi⟩, hsucc⟩
    constructor
    · have hz' : z = vempty H := (fEmptyF_spec H (scons z ee) 0).mp hz
      have hzi' : mem z (ee i) := hzi
      rwa [hz'] at hzi'
    · intro y hy
      obtain ⟨t, ht, hti⟩ := hsucc y hy
      have ht' : t = vsucc H y := (fSuccF_spec H (scons t (scons y ee)) 0 1).mp ht
      have hti' : mem t (ee i) := hti
      rwa [ht'] at hti'
  · intro ⟨he, hsucc⟩
    constructor
    · exact ⟨vempty H, (fEmptyF_spec H (scons (vempty H) ee) 0).mpr rfl, he⟩
    · intro y hy
      exact ⟨vsucc H y,
        (fSuccF_spec H (scons (vsucc H y) (scons y ee)) 0 1).mpr rfl,
        hsucc y hy⟩

noncomputable def omegaV (H : ZFAxioms mem) : V :=
  sepD H (fAll (fImp (fInd 0) (fMem 1 0))) (fun _ => vempty H) (InfSet H)

theorem omega_spec (H : ZFAxioms mem) (n : V) :
    mem n (omegaV H) ↔
      (mem n (InfSet H) ∧ ∀ c, inductiveV H c → mem n c) := by
  unfold omegaV
  rw [sepD_spec H (fAll (fImp (fInd 0) (fMem 1 0))) (fun _ => vempty H) (InfSet H) n]
  constructor
  · intro ⟨hI, h⟩
    refine ⟨hI, fun c hc => ?_⟩
    exact h c ((fInd_spec H (scons c (scons n (fun _ => vempty H))) 0).mpr hc)
  · intro ⟨hI, h⟩
    refine ⟨hI, fun c hc => ?_⟩
    exact h c ((fInd_spec H (scons c (scons n (fun _ => vempty H))) 0).mp hc)

theorem vempty_in_omega (H : ZFAxioms mem) : mem (vempty H) (omegaV H) :=
  (omega_spec H (vempty H)).mpr ⟨empty_in_InfSet H, fun _ hc => hc.1⟩

theorem omega_succ (H : ZFAxioms mem) (n : V) (hn : mem n (omegaV H)) :
    mem (vsucc H n) (omegaV H) := by
  obtain ⟨hI, h⟩ := (omega_spec H n).mp hn
  apply (omega_spec H (vsucc H n)).mpr
  refine ⟨vsucc_in_InfSet H n hI, fun c hc => ?_⟩
  exact hc.2 n (h c hc)

/-- THE DEFINABLE-INDUCTION SCHEMA: internal induction over omega for any
property given by a formula `phi` with parameters in the environment `e`. -/
theorem omega_ind (H : ZFAxioms mem) (phi : Form) (e : Nat → V)
    (hbase : Sat mem (scons (vempty H) e) phi)
    (hstep : ∀ n, mem n (omegaV H) → Sat mem (scons n e) phi →
      Sat mem (scons (vsucc H n) e) phi) :
    ∀ n, mem n (omegaV H) → Sat mem (scons n e) phi := by
  intro n hn
  have hA : ∀ x, mem x (sepD H phi e (omegaV H)) ↔
      (mem x (omegaV H) ∧ Sat mem (scons x e) phi) :=
    fun x => sepD_spec H phi e (omegaV H) x
  have hAind : inductiveV H (sepD H phi e (omegaV H)) := by
    constructor
    · exact (hA _).mpr ⟨vempty_in_omega H, hbase⟩
    · intro y hy
      obtain ⟨hyo, hyp⟩ := (hA y).mp hy
      exact (hA _).mpr ⟨omega_succ H y hyo, hstep y hyo hyp⟩
  obtain ⟨_, hleast⟩ := (omega_spec H n).mp hn
  exact ((hA n).mp (hleast _ hAind)).2

/-! ### Arithmetic of internal naturals -/

theorem nat_transitive (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) → ∀ y, mem y n → ∀ x, mem x y → mem x n := by
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (fun _ => omegaV H))
        (fAll (fImp (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 2))))) := by
    apply omega_ind H
    · intro y hy
      exact absurd hy (vempty_spec H y)
    · intro n hn IH y hy x hx
      apply (vsucc_spec H n x).mpr
      left
      rcases (vsucc_spec H n y).mp hy with hy | hy
      · exact IH y hy x hx
      · rw [hy] at hx; exact hx
  intro n hn y hy x hx
  exact h n hn y hy x hx

theorem nat_no_self (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) → ¬ mem n n := by
  have h : ∀ n, mem n (omegaV H) →
      Sat mem (scons n (fun _ => omegaV H)) (fImp (fMem 0 0) fBot) := by
    apply omega_ind H
    · intro hd
      exact vempty_spec H (vempty H) hd
    · intro n hn IH hd
      rcases (vsucc_spec H n (vsucc H n)).mp hd with hd | heq
      · exact IH (nat_transitive H n hn (vsucc H n) hd n (vsucc_self H n))
      · apply IH
        have hs := vsucc_self H n
        rwa [heq] at hs
  intro n hn
  exact h n hn

theorem succ_le_lt (H : ZFAxioms mem) (m : V) (hm : mem m (omegaV H)) (k : V)
    (h : mem (vsucc H k) m ∨ vsucc H k = m) : mem k m := by
  rcases h with hin | heq
  · exact nat_transitive H m hm (vsucc H k) hin k (vsucc_self H k)
  · have hs := vsucc_self H k
    rwa [heq] at hs

theorem succ_not_le (H : ZFAxioms mem) (m : V) (hm : mem m (omegaV H)) :
    ¬ (mem (vsucc H m) m ∨ vsucc H m = m) := fun h =>
  nat_no_self H m hm (succ_le_lt H m hm m h)

theorem succ_not_in_self (H : ZFAxioms mem) (m : V) (hm : mem m (omegaV H)) :
    ¬ mem (vsucc H m) (vsucc H m) :=
  nat_no_self H (vsucc H m) (omega_succ H m hm)

theorem succ_inj_nat (H : ZFAxioms mem) (m : V) (hm : mem m (omegaV H)) (k : V)
    (hkm : mem k m ∨ k = m) (heq : vsucc H k = vsucc H m) : k = m := by
  rcases hkm with hk | hk
  · exfalso
    have hs := vsucc_self H m
    rw [← heq] at hs
    rcases (vsucc_spec H k m).mp hs with hmk | hme
    · exact nat_no_self H m hm (nat_transitive H m hm k hk m hmk)
    · rw [hme] at hk hm
      exact nat_no_self H k hm hk
  · exact hk

/-! ## The closure construction for a fixed definable relation.

`psiC` is the formula defining the relation (argument slots 0, 1; parameters
in `eC` from slot 2 up), `relOf mem psiC eC` its semantic reading. -/

/-! ### The canonical one-step operator `gstep`, via FO Replacement -/

noncomputable def bnd {R : V → V → Prop} (HSL : SetLike mem R) (x : V) : V :=
  (HSL x).choose

theorem bnd_spec {R : V → V → Prop} (HSL : SetLike mem R) (x z : V)
    (h : R z x) : mem z (bnd HSL x) :=
  (HSL x).choose_spec z h

/-- The CANONICAL set of `RC`-predecessors of `v` (canonical by
Extensionality, even though the bound used to carve it is chosen by
Hilbert epsilon). -/
noncomputable def predSet (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (v : V) : V :=
  sepD H psiC (scons v eC) (bnd HSL v)

theorem predSet_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (v z : V) :
    mem z (predSet H psiC eC HSL v) ↔ relOf mem psiC eC z v := by
  unfold predSet
  rw [sepD_spec H psiC (scons v eC) (bnd HSL v) z]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨bnd_spec HSL v z h, h⟩

/-- The graph formula "slot 0 = the set of RC-predecessors of slot 1". -/
def rPS : Nat → Nat
  | 0 => 0
  | 1 => 2
  | k+2 => k+3

def psiPS (psiC : Form) : Form := fSetByF 0 (rename rPS psiC)

theorem psiPS_rel (psiC : Form) (eC : Nat → V) (y x : V) :
    relOf mem (psiPS psiC) eC y x ↔ (∀ u, mem u y ↔ relOf mem psiC eC u x) := by
  have hin : ∀ u : V,
      Sat mem (scons u (scons y (scons x eC))) (rename rPS psiC)
        ↔ relOf mem psiC eC u x := by
    intro u
    unfold relOf
    exact Sat_rename_ext psiC rPS _ _
      (fun n => match n with | 0 => rfl | 1 => rfl | _+2 => rfl)
  unfold relOf psiPS
  rw [fSetByF_sat]
  simp only [scons]
  constructor
  · intro h u
    have hu := h u
    exact ⟨fun hm => (hin u).mp (hu.1 hm), fun hr => hu.2 ((hin u).mpr hr)⟩
  · intro h u
    exact ⟨fun hm => (hin u).mpr ((h u).mp hm),
           fun hs => (h u).mpr ((hin u).mp hs)⟩

theorem psiPS_functional (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V) :
    Functional (relOf mem (psiPS psiC) eC) := by
  intro x y1 y2 h1 h2
  have g1 := (psiPS_rel psiC eC y1 x).mp h1
  have g2 := (psiPS_rel psiC eC y2 x).mp h2
  apply H.ext
  intro u
  rw [g1 u, g2 u]

noncomputable def predImg (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (t : V) : V :=
  (H.repl (psiPS psiC) eC (psiPS_functional H psiC eC) t).choose

theorem predImg_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V) (t y : V) :
    mem y (predImg H psiC eC t) ↔
      ∃ x, mem x t ∧ relOf mem (psiPS psiC) eC y x :=
  (H.repl (psiPS psiC) eC (psiPS_functional H psiC eC) t).choose_spec y

/-- `g(t) = t ∪ { u : ∃ v ∈ t, RC u v }` — the textbook one-step closure
operator, built canonically (no choice of bounds leaks in). -/
noncomputable def gstep (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (t : V) : V :=
  vcup H t (vunion H (predImg H psiC eC t))

theorem gstep_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (t u : V) :
    mem u (gstep H psiC eC t) ↔
      (mem u t ∨ ∃ v, mem v t ∧ relOf mem psiC eC u v) := by
  unfold gstep
  rw [vcup_spec H t (vunion H (predImg H psiC eC t)) u,
      vunion_spec H (predImg H psiC eC t) u]
  constructor
  · intro h
    rcases h with hl | ⟨y, huy, hy⟩
    · exact Or.inl hl
    right
    obtain ⟨x, hxt, hrel⟩ := (predImg_spec H psiC eC t y).mp hy
    have hrel' := (psiPS_rel psiC eC y x).mp hrel
    exact ⟨x, hxt, (hrel' u).mp huy⟩
  · intro h
    rcases h with hl | ⟨v, hvt, hrc⟩
    · exact Or.inl hl
    right
    refine ⟨predSet H psiC eC HSL v, (predSet_spec H psiC eC HSL v u).mpr hrc, ?_⟩
    apply (predImg_spec H psiC eC t (predSet H psiC eC HSL v)).mpr
    refine ⟨v, hvt, ?_⟩
    apply (psiPS_rel psiC eC _ v).mpr
    intro w
    exact predSet_spec H psiC eC HSL v w

/-! ### Relation- and step-macros, with the parameter block.

Formulas below mention `psiC`, so their specs carry the side condition that
the environment holds `eC`'s values from slot `off` upward. -/

def rRF (i j off : Nat) : Nat → Nat
  | 0 => i
  | 1 => j
  | k+2 => k + off

/-- "RC (slot `i`) (slot `j`)" -/
def fRF (psiC : Form) (i j off : Nat) : Form := rename (rRF i j off) psiC

theorem fRF_spec (psiC : Form) (eC : Nat → V) (ee : Nat → V) (i j off : Nat)
    (hoff : ∀ k, ee (k + off) = eC k) :
    Sat mem ee (fRF psiC i j off) ↔ relOf mem psiC eC (ee i) (ee j) := by
  unfold fRF relOf
  exact Sat_rename_ext psiC (rRF i j off) _ _
    (fun n => match n with | 0 => rfl | 1 => rfl | k+2 => hoff k)

/-- "slot `i` = gstep (slot `j`)" -/
def fStepF (psiC : Form) (i j off : Nat) : Form :=
  fSetByF i
    (fOr (fMem 0 (j+1))
      (fEx (fAnd (fMem 0 (j+2)) (fRF psiC 1 0 (off+2)))))

theorem fStepF_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (ee : Nat → V) (i j off : Nat)
    (hoff : ∀ k, ee (k + off) = eC k) :
    Sat mem ee (fStepF psiC i j off) ↔ ee i = gstep H psiC eC (ee j) := by
  have hin : ∀ u v : V,
      Sat mem (scons v (scons u ee)) (fRF psiC 1 0 (off+2))
        ↔ relOf mem psiC eC u v := by
    intro u v
    exact fRF_spec psiC eC (scons v (scons u ee)) 1 0 (off+2) (fun k => hoff k)
  apply fSetByF_spec H
  intro u
  change (mem u (ee j) ∨ ∃ v, mem v (ee j) ∧
      Sat mem (scons v (scons u ee)) (fRF psiC 1 0 (off+2))) ↔ _
  rw [gstep_spec H psiC eC HSL (ee j) u]
  constructor
  · rintro (hl | ⟨v, hv, hr⟩)
    · exact Or.inl hl
    · exact Or.inr ⟨v, hv, (hin u v).mp hr⟩
  · rintro (hl | ⟨v, hv, hr⟩)
    · exact Or.inl hl
    · exact Or.inr ⟨v, hv, (hin u v).mpr hr⟩

/-! ### The approximation predicate -/

/-- `Approx H psiC eC s f m`: `f` is (the graph of) a function with domain
`{0,…,m}` recording the iteration `s, g(s), g(g(s)), …` -/
def Approx (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V) (s f m : V) : Prop :=
  (∀ k y y', mem (kpair H k y) f → mem (kpair H k y') f → y = y') ∧
  (∀ k y, mem (kpair H k y) f → (mem k m ∨ k = m)) ∧
  mem (kpair H (vempty H) s) f ∧
  (∀ k, (mem k m ∨ k = m) → ∃ y, mem (kpair H k y) f) ∧
  (∀ k t y, mem k m → mem (kpair H k t) f → mem (kpair H (vsucc H k) y) f →
    y = gstep H psiC eC t)

/-- clause 1: functionality -/
def fAppC1 (f_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fAnd (fPairMemF 2 1 (f_i+3))
                               (fPairMemF 2 0 (f_i+3)))
                         (fEq 1 0))))

theorem fAppC1_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i : Nat) :
    Sat mem ee (fAppC1 f_i) ↔
      (∀ k y y', mem (kpair H k y) (ee f_i) → mem (kpair H k y') (ee f_i) →
        y = y') := by
  constructor
  · intro h k y y' h1 h2
    apply h k y y'
    constructor
    · exact (fPairMemF_spec H (scons y' (scons y (scons k ee))) 2 1 (f_i+3)).mpr h1
    · exact (fPairMemF_spec H (scons y' (scons y (scons k ee))) 2 0 (f_i+3)).mpr h2
  · intro h k y y' hc
    have h12 : Sat mem (scons y' (scons y (scons k ee))) (fPairMemF 2 1 (f_i+3)) ∧
        Sat mem (scons y' (scons y (scons k ee))) (fPairMemF 2 0 (f_i+3)) := hc
    exact h k y y'
      ((fPairMemF_spec H (scons y' (scons y (scons k ee))) 2 1 (f_i+3)).mp h12.1)
      ((fPairMemF_spec H (scons y' (scons y (scons k ee))) 2 0 (f_i+3)).mp h12.2)

/-- clause 2: the domain is bounded by `{0,…,m}` -/
def fAppC2 (f_i m_i : Nat) : Form :=
  fAll (fAll (fImp (fPairMemF 1 0 (f_i+2))
                   (fOr (fMem 1 (m_i+2)) (fEq 1 (m_i+2)))))

theorem fAppC2_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i m_i : Nat) :
    Sat mem ee (fAppC2 f_i m_i) ↔
      (∀ k y, mem (kpair H k y) (ee f_i) → (mem k (ee m_i) ∨ k = ee m_i)) := by
  constructor
  · intro h k y hp
    exact h k y ((fPairMemF_spec H (scons y (scons k ee)) 1 0 (f_i+2)).mpr hp)
  · intro h k y hp
    exact h k y ((fPairMemF_spec H (scons y (scons k ee)) 1 0 (f_i+2)).mp hp)

/-- clause 3: the base pair ⟨0, s⟩ is recorded -/
def fAppC3 (f_i s_i : Nat) : Form :=
  fEx (fAnd (fEmptyF 0) (fPairMemF 0 (s_i+1) (f_i+1)))

theorem fAppC3_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i s_i : Nat) :
    Sat mem ee (fAppC3 f_i s_i) ↔
      mem (kpair H (vempty H) (ee s_i)) (ee f_i) := by
  constructor
  · intro ⟨z, hz, hp⟩
    have hz' : z = vempty H := (fEmptyF_spec H (scons z ee) 0).mp hz
    have hp' : mem (kpair H z (ee s_i)) (ee f_i) :=
      (fPairMemF_spec H (scons z ee) 0 (s_i+1) (f_i+1)).mp hp
    rwa [hz'] at hp'
  · intro h
    refine ⟨vempty H, (fEmptyF_spec H (scons (vempty H) ee) 0).mpr rfl, ?_⟩
    exact (fPairMemF_spec H (scons (vempty H) ee) 0 (s_i+1) (f_i+1)).mpr h

/-- clause 4: the domain covers `{0,…,m}` -/
def fAppC4 (f_i m_i : Nat) : Form :=
  fAll (fImp (fOr (fMem 0 (m_i+1)) (fEq 0 (m_i+1)))
             (fEx (fPairMemF 1 0 (f_i+2))))

theorem fAppC4_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i m_i : Nat) :
    Sat mem ee (fAppC4 f_i m_i) ↔
      (∀ k, (mem k (ee m_i) ∨ k = ee m_i) → ∃ y, mem (kpair H k y) (ee f_i)) := by
  constructor
  · intro h k hk
    obtain ⟨y, hy⟩ := h k hk
    exact ⟨y, (fPairMemF_spec H (scons y (scons k ee)) 1 0 (f_i+2)).mp hy⟩
  · intro h k hk
    obtain ⟨y, hy⟩ := h k hk
    exact ⟨y, (fPairMemF_spec H (scons y (scons k ee)) 1 0 (f_i+2)).mpr hy⟩

/-- clause 5: the recurrence `f(k+1) = gstep (f k)` -/
def fAppC5 (psiC : Form) (f_i m_i off : Nat) : Form :=
  fAll (fAll (fAll (fAll
    (fImp (fAnd (fAnd (fAnd (fMem 3 (m_i+4)) (fSuccF 2 3))
                      (fPairMemF 3 1 (f_i+4)))
                (fPairMemF 2 0 (f_i+4)))
          (fStepF psiC 0 1 (off+4))))))

theorem fAppC5_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (ee : Nat → V) (f_i m_i off : Nat)
    (hoff : ∀ k, ee (k + off) = eC k) :
    Sat mem ee (fAppC5 psiC f_i m_i off) ↔
      (∀ k t y, mem k (ee m_i) → mem (kpair H k t) (ee f_i) →
        mem (kpair H (vsucc H k) y) (ee f_i) → y = gstep H psiC eC t) := by
  constructor
  · intro h k t y hk h1 h2
    have hc : Sat mem (scons y (scons t (scons (vsucc H k) (scons k ee))))
        (fStepF psiC 0 1 (off+4)) := by
      apply h k (vsucc H k) t y
      refine ⟨⟨⟨hk, ?_⟩, ?_⟩, ?_⟩
      · exact (fSuccF_spec H (scons y (scons t (scons (vsucc H k) (scons k ee)))) 2 3).mpr rfl
      · exact (fPairMemF_spec H (scons y (scons t (scons (vsucc H k) (scons k ee)))) 3 1 (f_i+4)).mpr h1
      · exact (fPairMemF_spec H (scons y (scons t (scons (vsucc H k) (scons k ee)))) 2 0 (f_i+4)).mpr h2
    exact (fStepF_spec H psiC eC HSL
      (scons y (scons t (scons (vsucc H k) (scons k ee)))) 0 1 (off+4)
      (fun k0 => hoff k0)).mp hc
  · intro h d d0 d1 d2 hc
    have hc' : ((Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fMem 3 (m_i+4)) ∧
                 Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fSuccF 2 3)) ∧
                Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fPairMemF 3 1 (f_i+4))) ∧
               Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fPairMemF 2 0 (f_i+4)) := hc
    obtain ⟨⟨⟨hk, hsucc⟩, hP1⟩, hP2⟩ := hc'
    have hsucc' : d0 = vsucc H d :=
      (fSuccF_spec H (scons d2 (scons d1 (scons d0 (scons d ee)))) 2 3).mp hsucc
    have hP1' : mem (kpair H d d1) (ee f_i) :=
      (fPairMemF_spec H (scons d2 (scons d1 (scons d0 (scons d ee)))) 3 1 (f_i+4)).mp hP1
    have hP2' : mem (kpair H d0 d2) (ee f_i) :=
      (fPairMemF_spec H (scons d2 (scons d1 (scons d0 (scons d ee)))) 2 0 (f_i+4)).mp hP2
    apply (fStepF_spec H psiC eC HSL
      (scons d2 (scons d1 (scons d0 (scons d ee)))) 0 1 (off+4)
      (fun k0 => hoff k0)).mpr
    rw [hsucc'] at hP2'
    exact h d d1 d2 hk hP1' hP2'

/-- the full approximation formula -/
def fApproxF (psiC : Form) (f_i m_i s_i off : Nat) : Form :=
  fAnd (fAppC1 f_i)
       (fAnd (fAppC2 f_i m_i)
             (fAnd (fAppC3 f_i s_i)
                   (fAnd (fAppC4 f_i m_i) (fAppC5 psiC f_i m_i off))))

theorem fApproxF_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) (ee : Nat → V)
    (f_i m_i s_i off : Nat)
    (hoff : ∀ k, ee (k + off) = eC k) (hs : ee s_i = s) :
    Sat mem ee (fApproxF psiC f_i m_i s_i off) ↔
      Approx H psiC eC s (ee f_i) (ee m_i) := by
  constructor
  · intro hc
    have hc' : Sat mem ee (fAppC1 f_i) ∧
        (Sat mem ee (fAppC2 f_i m_i) ∧
          (Sat mem ee (fAppC3 f_i s_i) ∧
            (Sat mem ee (fAppC4 f_i m_i) ∧
              Sat mem ee (fAppC5 psiC f_i m_i off)))) := hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc'
    refine ⟨(fAppC1_spec H ee f_i).mp h1, (fAppC2_spec H ee f_i m_i).mp h2,
            ?_, (fAppC4_spec H ee f_i m_i).mp h4,
            (fAppC5_spec H psiC eC HSL ee f_i m_i off hoff).mp h5⟩
    have := (fAppC3_spec H ee f_i s_i).mp h3
    rwa [hs] at this
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(fAppC1_spec H ee f_i).mpr h1,
            (fAppC2_spec H ee f_i m_i).mpr h2,
            ?_,
            (fAppC4_spec H ee f_i m_i).mpr h4,
            (fAppC5_spec H psiC eC HSL ee f_i m_i off hoff).mpr h5⟩
    apply (fAppC3_spec H ee f_i s_i).mpr
    rw [hs]
    exact h3

/-! ### The stage relation `Theta` and its formula -/

def Theta (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V) (s : V)
    (y m : V) : Prop :=
  mem m (omegaV H) ∧ ∃ f, Approx H psiC eC s f m ∧ mem (kpair H m y) f

def fThetaF (psiC : Form) (y_i m_i s_i om_i off : Nat) : Form :=
  fAnd (fMem m_i om_i)
       (fEx (fAnd (fApproxF psiC 0 (m_i+1) (s_i+1) (off+1))
                  (fPairMemF (m_i+1) (y_i+1) 0)))

theorem fThetaF_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) (ee : Nat → V)
    (y_i m_i s_i om_i off : Nat)
    (hoff : ∀ k, ee (k + off) = eC k) (hs : ee s_i = s)
    (hom : ee om_i = omegaV H) :
    Sat mem ee (fThetaF psiC y_i m_i s_i om_i off) ↔
      Theta H psiC eC s (ee y_i) (ee m_i) := by
  unfold Theta
  constructor
  · intro hc
    have hc' : mem (ee m_i) (ee om_i) ∧
        ∃ f, Sat mem (scons f ee) (fApproxF psiC 0 (m_i+1) (s_i+1) (off+1)) ∧
             Sat mem (scons f ee) (fPairMemF (m_i+1) (y_i+1) 0) := hc
    obtain ⟨hm, f, hA, hP⟩ := hc'
    rw [hom] at hm
    refine ⟨hm, f, ?_, ?_⟩
    · exact (fApproxF_spec H psiC eC HSL s (scons f ee) 0 (m_i+1) (s_i+1) (off+1)
        (fun k => hoff k) hs).mp hA
    · exact (fPairMemF_spec H (scons f ee) (m_i+1) (y_i+1) 0).mp hP
  · intro ⟨hm, f, hA, hP⟩
    refine ⟨?_, f, ?_, ?_⟩
    · show mem (ee m_i) (ee om_i)
      rw [hom]; exact hm
    · exact (fApproxF_spec H psiC eC HSL s (scons f ee) 0 (m_i+1) (s_i+1) (off+1)
        (fun k => hoff k) hs).mpr hA
    · exact (fPairMemF_spec H (scons f ee) (m_i+1) (y_i+1) 0).mpr hP

def psiTheta (psiC : Form) : Form := fThetaF psiC 0 1 2 3 4

noncomputable def eTheta (H : ZFAxioms mem) (eC : Nat → V) (s : V) : Nat → V :=
  scons s (scons (omegaV H) eC)

theorem theta_rel (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) (y m : V) :
    relOf mem (psiTheta psiC) (eTheta H eC s) y m ↔ Theta H psiC eC s y m :=
  fThetaF_spec H psiC eC HSL s (scons y (scons m (eTheta H eC s))) 0 1 2 3 4
    (fun _ => rfl) rfl rfl

/-! ### Existence of approximations -/

theorem Approx_base (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V) (s : V) :
    Approx H psiC eC s (vsingle H (kpair H (vempty H) s)) (vempty H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k y y' h1 h2
    have h1' := (vsingle_spec H (kpair H (vempty H) s) (kpair H k y)).mp h1
    have h2' := (vsingle_spec H (kpair H (vempty H) s) (kpair H k y')).mp h2
    have hy := (kpair_inj H k y (vempty H) s h1').2
    have hy' := (kpair_inj H k y' (vempty H) s h2').2
    rw [hy, hy']
  · intro k y h
    have h' := (vsingle_spec H (kpair H (vempty H) s) (kpair H k y)).mp h
    exact Or.inr (kpair_inj H k y (vempty H) s h').1
  · exact (vsingle_spec H (kpair H (vempty H) s) (kpair H (vempty H) s)).mpr rfl
  · intro k hk
    rcases hk with hk | hk
    · exact absurd hk (vempty_spec H k)
    · refine ⟨s, ?_⟩
      rw [hk]
      exact (vsingle_spec H (kpair H (vempty H) s) (kpair H (vempty H) s)).mpr rfl
  · intro k t y hk _ _
    exact absurd hk (vempty_spec H k)

theorem Approx_extend (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (s : V) (m f t : V) (hm : mem m (omegaV H))
    (hA : Approx H psiC eC s f m) (hmt : mem (kpair H m t) f) :
    Approx H psiC eC s
      (vcup H f (vsingle H (kpair H (vsucc H m) (gstep H psiC eC t))))
      (vsucc H m) := by
  obtain ⟨C1, C2, C3, C4, C5⟩ := hA
  have hf' : ∀ x, mem x (vcup H f (vsingle H (kpair H (vsucc H m) (gstep H psiC eC t))))
      ↔ (mem x f ∨ x = kpair H (vsucc H m) (gstep H psiC eC t)) := by
    intro x
    rw [vcup_spec H f (vsingle H (kpair H (vsucc H m) (gstep H psiC eC t))) x,
        vsingle_spec H (kpair H (vsucc H m) (gstep H psiC eC t)) x]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- functionality
    intro k y y' h1 h2
    rcases (hf' (kpair H k y)).mp h1 with h1 | h1 <;>
      rcases (hf' (kpair H k y')).mp h2 with h2 | h2
    · exact C1 k y y' h1 h2
    · exfalso
      have hk := (kpair_inj H k y' (vsucc H m) (gstep H psiC eC t) h2).1
      rw [hk] at h1
      exact succ_not_le H m hm (C2 (vsucc H m) y h1)
    · exfalso
      have hk := (kpair_inj H k y (vsucc H m) (gstep H psiC eC t) h1).1
      rw [hk] at h2
      exact succ_not_le H m hm (C2 (vsucc H m) y' h2)
    · have hy := (kpair_inj H k y (vsucc H m) (gstep H psiC eC t) h1).2
      have hy' := (kpair_inj H k y' (vsucc H m) (gstep H psiC eC t) h2).2
      rw [hy, hy']
  · -- domain bound
    intro k y h
    rcases (hf' (kpair H k y)).mp h with h | h
    · rcases C2 k y h with hk | hk
      · exact Or.inl ((vsucc_spec H m k).mpr (Or.inl hk))
      · exact Or.inl ((vsucc_spec H m k).mpr (Or.inr hk))
    · exact Or.inr (kpair_inj H k y (vsucc H m) (gstep H psiC eC t) h).1
  · -- base pair
    exact (hf' (kpair H (vempty H) s)).mpr (Or.inl C3)
  · -- domain coverage
    intro k hk
    rcases hk with hk | hk
    · obtain ⟨y, hy⟩ := C4 k ((vsucc_spec H m k).mp hk)
      exact ⟨y, (hf' (kpair H k y)).mpr (Or.inl hy)⟩
    · refine ⟨gstep H psiC eC t, (hf' _).mpr (Or.inr ?_)⟩
      rw [hk]
  · -- recurrence
    intro k t' y hk h1 h2
    have h1' := (hf' (kpair H k t')).mp h1
    have h2' := (hf' (kpair H (vsucc H k) y)).mp h2
    have hk' := (vsucc_spec H m k).mp hk
    rcases h1' with h1' | h1'
    · rcases h2' with h2' | h2'
      · rcases hk' with hk' | hk'
        · exact C5 k t' y hk' h1' h2'
        · exfalso
          rw [hk'] at h2'
          exact succ_not_le H m hm (C2 (vsucc H m) y h2')
      · obtain ⟨hsk, hy⟩ :=
          kpair_inj H (vsucc H k) y (vsucc H m) (gstep H psiC eC t) h2'
        have hkm : k = m := succ_inj_nat H m hm k hk' hsk
        rw [hkm] at h1'
        have htt : t' = t := C1 m t' t h1' hmt
        rw [hy, htt]
    · obtain ⟨hk'', _⟩ :=
        kpair_inj H k t' (vsucc H m) (gstep H psiC eC t) h1'
      exfalso
      rw [hk''] at hk'
      exact succ_not_le H m hm hk'

/-- Existence of approximations, by internal induction. -/
theorem Approx_exists (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) :
    ∀ m, mem m (omegaV H) → ∃ f, Approx H psiC eC s f m := by
  have hbr : ∀ n : V,
      Sat mem (scons n (scons s eC)) (fEx (fApproxF psiC 0 1 2 3)) ↔
        ∃ f, Approx H psiC eC s f n := by
    intro n
    constructor
    · intro ⟨f, hf⟩
      exact ⟨f, (fApproxF_spec H psiC eC HSL s
        (scons f (scons n (scons s eC))) 0 1 2 3 (fun _ => rfl) rfl).mp hf⟩
    · intro ⟨f, hf⟩
      exact ⟨f, (fApproxF_spec H psiC eC HSL s
        (scons f (scons n (scons s eC))) 0 1 2 3 (fun _ => rfl) rfl).mpr hf⟩
  intro m hm
  apply (hbr m).mp
  apply omega_ind H (fEx (fApproxF psiC 0 1 2 3)) (scons s eC) ?_ ?_ m hm
  · exact (hbr (vempty H)).mpr
      ⟨vsingle H (kpair H (vempty H) s), Approx_base H psiC eC s⟩
  · intro n hn IH
    apply (hbr (vsucc H n)).mpr
    obtain ⟨f, hf⟩ := (hbr n).mp IH
    obtain ⟨t, ht⟩ := hf.2.2.2.1 n (Or.inr rfl)
    exact ⟨vcup H f (vsingle H (kpair H (vsucc H n) (gstep H psiC eC t))),
      Approx_extend H psiC eC s n f t hn hf ht⟩

/-! ### Uniqueness (agreement) -/

theorem Approx_agree (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (s : V) (m : V) (hm : mem m (omegaV H)) (f f' : V)
    (hf : Approx H psiC eC s f m) (hf' : Approx H psiC eC s f' m) :
    ∀ k, mem k (omegaV H) →
      ∀ y y', (mem k m ∨ k = m) →
        mem (kpair H k y) f → mem (kpair H k y') f' → y = y' := by
  have hbr : ∀ k : V,
      Sat mem (scons k (scons f (scons f' (scons m (fun _ => vempty H)))))
        (fAll (fAll (fImp
          (fAnd (fAnd (fOr (fMem 2 5) (fEq 2 5)) (fPairMemF 2 1 3))
                (fPairMemF 2 0 4))
          (fEq 1 0)))) ↔
      (∀ y y', (mem k m ∨ k = m) →
        mem (kpair H k y) f → mem (kpair H k y') f' → y = y') := by
    intro k
    constructor
    · intro h y y' hkm h1 h2
      apply h y y'
      refine ⟨⟨hkm, ?_⟩, ?_⟩
      · exact (fPairMemF_spec H
          (scons y' (scons y (scons k (scons f (scons f' (scons m (fun _ => vempty H)))))))
          2 1 3).mpr h1
      · exact (fPairMemF_spec H
          (scons y' (scons y (scons k (scons f (scons f' (scons m (fun _ => vempty H)))))))
          2 0 4).mpr h2
    · intro h y y' hc
      have hc' : ((mem k m ∨ k = m) ∧
          Sat mem (scons y' (scons y (scons k (scons f (scons f' (scons m (fun _ => vempty H)))))))
            (fPairMemF 2 1 3)) ∧
          Sat mem (scons y' (scons y (scons k (scons f (scons f' (scons m (fun _ => vempty H)))))))
            (fPairMemF 2 0 4) := hc
      obtain ⟨⟨hkm, hP1⟩, hP2⟩ := hc'
      exact h y y' hkm
        ((fPairMemF_spec H _ 2 1 3).mp hP1)
        ((fPairMemF_spec H _ 2 0 4).mp hP2)
  intro k hk
  apply (hbr k).mp
  apply omega_ind H _ (scons f (scons f' (scons m (fun _ => vempty H)))) ?_ ?_ k hk
  · -- base: both functions record s at 0
    apply (hbr (vempty H)).mpr
    intro y y' _ h1 h2
    obtain ⟨C1, _, C3, _, _⟩ := hf
    obtain ⟨C1', _, C3', _, _⟩ := hf'
    calc y = s := C1 (vempty H) y s h1 C3
      _ = y' := (C1' (vempty H) y' s h2 C3').symm
  · -- step
    intro n hn IH
    apply (hbr (vsucc H n)).mpr
    have IH' := (hbr n).mp IH
    intro y y' hsm h1 h2
    have hnm : mem n m := succ_le_lt H m hm n hsm
    obtain ⟨C1, C2, C3, C4, C5⟩ := hf
    obtain ⟨C1', C2', C3', C4', C5'⟩ := hf'
    obtain ⟨t, ht⟩ := C4 n (Or.inl hnm)
    obtain ⟨t', ht'⟩ := C4' n (Or.inl hnm)
    have htt : t = t' := IH' t t' (Or.inl hnm) ht ht'
    rw [C5 n t y hnm ht h1, C5' n t' y' hnm ht' h2, htt]

theorem theta_functional (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) :
    Functional (relOf mem (psiTheta psiC) (eTheta H eC s)) := by
  intro m y1 y2 h1 h2
  have h1' := (theta_rel H psiC eC HSL s y1 m).mp h1
  have h2' := (theta_rel H psiC eC HSL s y2 m).mp h2
  obtain ⟨hm, f, hf, hp⟩ := h1'
  obtain ⟨_, f', hf', hp'⟩ := h2'
  exact Approx_agree H psiC eC s m hm f f' hf hf' m hm y1 y2 (Or.inr rfl) hp hp'

/-! ### Collect the stages with FO Replacement, take the union -/

noncomputable def Wimg (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) : V :=
  (H.repl (psiTheta psiC) (eTheta H eC s)
    (theta_functional H psiC eC HSL s) (omegaV H)).choose

theorem Wimg_spec (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) (y : V) :
    mem y (Wimg H psiC eC HSL s) ↔
      ∃ mm, mem mm (omegaV H) ∧
        relOf mem (psiTheta psiC) (eTheta H eC s) y mm :=
  (H.repl (psiTheta psiC) (eTheta H eC s)
    (theta_functional H psiC eC HSL s) (omegaV H)).choose_spec y

/-- Every definable set-like relation admits a closure superset of any
seed — inside every first-order model of {Ext, Sep, Pair, Union, Inf, Repl}
(no Powerset, no Regularity). -/
theorem ClosureFO_of_ZF (H : ZFAxioms mem) (psiC : Form) (eC : Nat → V)
    (HSL : SetLike mem (relOf mem psiC eC)) (s : V) :
    ∃ w, Sub mem s w ∧
      ∀ u v, relOf mem psiC eC u v → mem v w → mem u w := by
  refine ⟨vunion H (Wimg H psiC eC HSL s), ?_, ?_⟩
  · -- s is contained: s itself is stage 0
    intro x hx
    apply (vunion_spec H (Wimg H psiC eC HSL s) x).mpr
    refine ⟨s, hx, ?_⟩
    apply (Wimg_spec H psiC eC HSL s s).mpr
    refine ⟨vempty H, vempty_in_omega H, ?_⟩
    apply (theta_rel H psiC eC HSL s s (vempty H)).mpr
    refine ⟨vempty_in_omega H, vsingle H (kpair H (vempty H) s),
      Approx_base H psiC eC s, ?_⟩
    exact (vsingle_spec H (kpair H (vempty H) s) (kpair H (vempty H) s)).mpr rfl
  · -- closed under RC-predecessors: step to the next stage
    intro u v hR hv
    obtain ⟨y, hvy, hyW⟩ := (vunion_spec H (Wimg H psiC eC HSL s) v).mp hv
    obtain ⟨mm, hmm, hT⟩ := (Wimg_spec H psiC eC HSL s y).mp hyW
    obtain ⟨_, f, hf, hp⟩ := (theta_rel H psiC eC HSL s y mm).mp hT
    apply (vunion_spec H (Wimg H psiC eC HSL s) u).mpr
    refine ⟨gstep H psiC eC y, ?_, ?_⟩
    · exact (gstep_spec H psiC eC HSL y u).mpr (Or.inr ⟨v, hvy, hR⟩)
    · apply (Wimg_spec H psiC eC HSL s (gstep H psiC eC y)).mpr
      refine ⟨vsucc H mm, omega_succ H mm hmm, ?_⟩
      apply (theta_rel H psiC eC HSL s (gstep H psiC eC y) (vsucc H mm)).mpr
      refine ⟨omega_succ H mm hmm,
        vcup H f (vsingle H (kpair H (vsucc H mm) (gstep H psiC eC y))),
        Approx_extend H psiC eC s mm f y hmm hf hp, ?_⟩
      apply (vcup_spec H f
        (vsingle H (kpair H (vsucc H mm) (gstep H psiC eC y)))
        (kpair H (vsucc H mm) (gstep H psiC eC y))).mpr
      exact Or.inr ((vsingle_spec H _ _).mpr rfl)

end ZfModel

end SetTheory
