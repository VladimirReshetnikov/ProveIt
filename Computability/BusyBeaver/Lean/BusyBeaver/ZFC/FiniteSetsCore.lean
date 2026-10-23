import BusyBeaver.ZFC.SingletonInfinityCore
import ZF.Zf

/-!
Finite set constructors and literal graph atoms without Infinity.
The elementary operator and Kuratowski proofs are adapted from the repository's
ZF/Zf.lean, with their hypotheses reduced to Extensionality, Pairing and Union.
The inherited Separation field is used by the later finite-attempt construction;
no internal omega or recursion theorem is used here.
-/

namespace SetTheory.BusyBeaver.ZFC.FiniteSets
open Form
universe u
variable {V : Type u} {mem : V → V → Prop}

structure Base (mem : V → V → Prop) : Prop extends SingletonInfinity.Base mem where
  union : ∀ a, ∃ b, ∀ z, mem z b ↔ ∃ x, mem z x ∧ mem x a

noncomputable def pair (H : Base mem) (a b : V) : V := (H.pair a b).choose

theorem pair_spec (H : Base mem) (a b x : V) :
    mem x (pair H a b) ↔ (x = a ∨ x = b) :=
  (H.pair a b).choose_spec x

noncomputable abbrev singleton (H : Base mem) (a : V) : V :=
  SingletonInfinity.singleton H.toBase a

theorem singleton_spec (H : Base mem) (a x : V) :
    mem x (singleton H a) ↔ x = a := SingletonInfinity.singleton_spec H.toBase a x

noncomputable def union (H : Base mem) (u : V) : V := (H.union u).choose

theorem union_spec (H : Base mem) (u x : V) :
    mem x (union H u) ↔ ∃ v, mem x v ∧ mem v u :=
  (H.union u).choose_spec x

noncomputable def cup (H : Base mem) (a b : V) : V := union H (pair H a b)

theorem cup_spec (H : Base mem) (a b x : V) :
    mem x (cup H a b) ↔ (mem x a ∨ mem x b) := by
  unfold cup
  rw [union_spec H (pair H a b) x]
  exact ⟨fun ⟨v, hxv, hv⟩ =>
      ((pair_spec H a b v).mp hv).imp (fun (e : v = a) => e ▸ hxv)
        fun (e : v = b) => e ▸ hxv,
    fun h => h.elim (fun ha => ⟨a, ha, (pair_spec H a b a).mpr (Or.inl rfl)⟩)
      fun hb => ⟨b, hb, (pair_spec H a b b).mpr (Or.inr rfl)⟩⟩

noncomputable def succ (H : Base mem) (a : V) : V := cup H a (singleton H a)

theorem succ_spec (H : Base mem) (a x : V) :
    mem x (succ H a) ↔ (mem x a ∨ x = a) := by
  unfold succ
  rw [cup_spec H a (singleton H a) x, singleton_spec H a x]

noncomputable def kpair (H : Base mem) (a b : V) : V :=
  pair H (singleton H a) (pair H a b)

theorem kpair_mem (H : Base mem) (a b q : V) :
    mem q (kpair H a b) ↔ (q = singleton H a ∨ q = pair H a b) :=
  pair_spec H _ _ q

theorem singleton_inj (H : Base mem) (a b : V)
    (h : singleton H a = singleton H b) : a = b :=
  (singleton_spec H b a).mp (h ▸ (singleton_spec H a a).mpr rfl)

theorem pair_single (H : Base mem) (a b c : V)
    (h : pair H a b = singleton H c) : a = c ∧ b = c :=
  ⟨(singleton_spec H c a).mp (h ▸ (pair_spec H a b a).mpr (Or.inl rfl)),
    (singleton_spec H c b).mp (h ▸ (pair_spec H a b b).mpr (Or.inr rfl))⟩

theorem kpair_inj (H : Base mem) {a b c d : V}
    (h : kpair H a b = kpair H c d) : a = c ∧ b = d := by
  have hac : a = c := ((kpair_mem H c d (singleton H a)).mp
    (h ▸ (kpair_mem H a b _).mpr (Or.inl rfl))).elim (singleton_inj H a c)
    fun hs => (pair_single H c d a hs.symm).1.symm
  refine ⟨hac, ?_⟩
  subst hac
  -- h : kpair a b = kpair a d
  have h1 : mem (pair H a b) (kpair H a b) :=
    (kpair_mem H a b _).mpr (Or.inr rfl)
  rw [h] at h1
  rcases (kpair_mem H a d _).mp h1 with h1 | h1
  · -- pair a b = singleton a, so b = a
    have hba : b = a := (pair_single H a b a h1).2
    have h2 : mem (pair H a d) (kpair H a d) :=
      (kpair_mem H a d _).mpr (Or.inr rfl)
    rw [← h] at h2
    rcases (kpair_mem H a b _).mp h2 with h2 | h2
    · exact hba.trans (pair_single H a d a h2).2.symm
    · exact ((pair_spec H a b d).mp (h2 ▸ (pair_spec H a d d).mpr (Or.inr rfl))).elim
        (fun hd => hba.trans hd.symm) Eq.symm
  · -- pair a b = pair a d
    refine ((pair_spec H a d b).mp (h1 ▸ (pair_spec H a b b).mpr (Or.inr rfl))).elim
      (fun hb => ?_) id
    -- b = a
    exact ((pair_spec H a b d).mp (h1 ▸ (pair_spec H a d d).mpr (Or.inr rfl))).elim
      (fun hd => hb.trans hd.symm) Eq.symm

noncomputable def insert (B : Base mem) (f p : V) : V := cup B f (singleton B p)

theorem insert_spec (B : Base mem) (f p z : V) :
    mem z (insert B f p) ↔ mem z f ∨ z = p := by
  rw [insert, cup_spec B, singleton_spec B]

/-- An actual set-by-formula specification, requiring only Extensionality. -/
theorem sat_setBy (B : Base mem) (env : Nat → V) (i : Nat) (phi : Form) (b : V)
    (hp : ∀ x, Sat mem (scons x env) phi ↔ mem x b) :
    Sat mem env (fSetByF i phi) ↔ env i = b := by
  rw [fSetByF_sat]
  exact ⟨fun h => B.ext _ _ fun x => (h x).trans (hp x), fun h x => by rw [h]; exact (hp x).symm⟩

/-- Inputs i,j; output k. -/
def pairForm (i j k : Nat) : Form :=
  fSetByF k (fOr (fEq 0 (i + 1)) (fEq 0 (j + 1)))

theorem sat_pairForm (B : Base mem) (env : Nat → V) (i j k : Nat) :
    Sat mem env (pairForm i j k) ↔ env k = pair B (env i) (env j) :=
  sat_setBy B env k _ _ fun x => (pair_spec B (env i) (env j) x).symm

/-- Inputs i,j; output k, with Kuratowski coding. -/
def kpairForm (i j k : Nat) : Form :=
  fSetByF k (fOr (SingletonInfinity.singForm (i + 1) 0) (pairForm (i + 1) (j + 1) 0))

theorem sat_kpairForm (B : Base mem) (env : Nat → V) (i j k : Nat) :
    Sat mem env (kpairForm i j k) ↔ env k = kpair B (env i) (env j) := by
  refine sat_setBy B env k _ _ fun x => ?_
  change (Sat mem (scons x env) (SingletonInfinity.singForm (i + 1) 0) ∨
    Sat mem (scons x env) (pairForm (i + 1) (j + 1) 0)) ↔ _
  rw [SingletonInfinity.sat_singForm B.toBase, sat_pairForm B, kpair_mem B]
  rfl

/-- Graph f contains the ordered pair (x,y). -/
def appForm (f x y : Nat) : Form :=
  fEx (fAnd (kpairForm (x + 1) (y + 1) 0) (fMem 0 (f + 1)))

theorem sat_appForm (B : Base mem) (env : Nat → V) (f x y : Nat) :
    Sat mem env (appForm f x y) ↔ mem (kpair B (env x) (env y)) (env f) := by
  refine ⟨fun ⟨p, hp, hm⟩ => ?_,
    fun hm => ⟨kpair B (env x) (env y), (sat_kpairForm B _ _ _ _).mpr rfl, hm⟩⟩
  have hp' : p = kpair B (env x) (env y) := (sat_kpairForm B _ _ _ _).mp hp
  change mem p (env f) at hm
  rwa [hp'] at hm

/-- Input i; output j, for the von Neumann successor. -/
def succForm (i j : Nat) : Form :=
  fSetByF j (fOr (fMem 0 (i + 1)) (fEq 0 (i + 1)))

theorem sat_succForm (B : Base mem) (env : Nat → V) (i j : Nat) :
    Sat mem env (succForm i j) ↔ env j = succ B (env i) :=
  sat_setBy B env j _ _ fun x => (succ_spec B (env i) x).symm

end SetTheory.BusyBeaver.ZFC.FiniteSets
