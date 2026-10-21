/-
  Fol.lean

  GENERIC first-order logic over the language of set theory: one binary
  relation symbol (rendered fMem) and equality (fEq), with De Bruijn
  variables.  Nothing in this file mentions any particular theory.

  Lean 4 port of the Rocq/Coq development `Logic/FirstOrder/Coq/Fol.v`.
  Statement-for-statement faithful; proofs re-idiomatized for Lean.

  - Created (UTC): 2026-07-01T00:00:00Z  (see git history for exact stamp)
-/

namespace SetTheory

/-! ## Cantor pairing (self-contained replacement for Coq's Stdlib Cantor) -/

namespace Cantor

/-- Triangular numbers, defined recursively (no division). -/
def tri : Nat → Nat
  | 0 => 0
  | n+1 => tri n + n + 1

/-- The Cantor pairing function: `toNat (x, y) = y + tri (x + y)`. -/
def toNat (p : Nat × Nat) : Nat := p.2 + tri (p.1 + p.2)

/-- Inverse of the pairing: walk the anti-diagonals. -/
def ofNat : Nat → Nat × Nat
  | 0 => (0, 0)
  | n+1 =>
    match ofNat n with
    | (0, y) => (y+1, 0)
    | (x+1, y) => (x, y+1)

theorem toNat_ofNat : ∀ n, toNat (ofNat n) = n
  | 0 => rfl
  | n+1 => by
    have ih := toNat_ofNat n
    show toNat (match ofNat n with
      | (0, y) => (y+1, 0)
      | (x+1, y) => (x, y+1)) = n+1
    cases h : ofNat n with
    | mk x y =>
      rw [h] at ih
      cases x with
      | zero => simp [toNat, tri] at ih ⊢; omega
      | succ x' =>
        simp [toNat] at ih ⊢
        have harg : x' + (y + 1) = x' + 1 + y := by omega
        rw [harg]; omega

theorem tri_le (n : Nat) : n ≤ tri n := by
  induction n with
  | zero => simp [tri]
  | succ n ih => simp only [tri]; omega

theorem tri_mono : ∀ {m n : Nat}, m ≤ n → tri m ≤ tri n := by
  intro m n h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [tri]; omega

theorem toNat_inj {p q : Nat × Nat} (h : toNat p = toNat q) : p = q := by
  obtain ⟨x1, y1⟩ := p; obtain ⟨x2, y2⟩ := q
  simp [toNat] at h
  have hs : x1 + y1 = x2 + y2 := by
    rcases Nat.lt_trichotomy (x1 + y1) (x2 + y2) with hlt | heq | hgt
    · have hm := tri_mono (Nat.succ_le_of_lt hlt)
      simp only [tri] at hm; omega
    · exact heq
    · have hm := tri_mono (Nat.succ_le_of_lt hgt)
      simp only [tri] at hm; omega
  have ht : tri (x1 + y1) = tri (x2 + y2) := by rw [hs]
  simp only [Prod.mk.injEq]
  omega

theorem ofNat_toNat (p : Nat × Nat) : ofNat (toNat p) = p :=
  toNat_inj (toNat_ofNat (toNat p))

/-- Both components are dominated by the code: `x + y ≤ toNat (x, y)`. -/
theorem add_le_toNat (x y : Nat) : x + y ≤ toNat (x, y) := by
  have := tri_le (x + y); simp [toNat]; omega

end Cantor

/-! ## Syntax: formulas and renaming -/

inductive Form : Type
  | fMem : Nat → Nat → Form
  | fEq  : Nat → Nat → Form
  | fBot : Form
  | fImp : Form → Form → Form
  | fAnd : Form → Form → Form
  | fOr  : Form → Form → Form
  | fAll : Form → Form
  | fEx  : Form → Form
  deriving Repr, DecidableEq

open Form

def fIff (a b : Form) : Form := fAnd (fImp a b) (fImp b a)

/-! ### Renaming of De Bruijn variables -/

def up (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => r k + 1

def rename (r : Nat → Nat) : Form → Form
  | fMem i j => fMem (r i) (r j)
  | fEq i j  => fEq (r i) (r j)
  | fBot     => fBot
  | fImp a b => fImp (rename r a) (rename r b)
  | fAnd a b => fAnd (rename r a) (rename r b)
  | fOr a b  => fOr (rename r a) (rename r b)
  | fAll a   => fAll (rename (up r) a)
  | fEx a    => fEx (rename (up r) a)

/-- Instantiate De Bruijn 0 by variable `k` (and decrement the rest). -/
def inst (k : Nat) : Nat → Nat
  | 0 => k
  | m+1 => m

/-! ### Free variables, and the equational theory of renaming -/

def Free : Nat → Form → Prop
  | n, fMem i j => n = i ∨ n = j
  | n, fEq i j  => n = i ∨ n = j
  | _, fBot     => False
  | n, fImp a b => Free n a ∨ Free n b
  | n, fAnd a b => Free n a ∨ Free n b
  | n, fOr a b  => Free n a ∨ Free n b
  | n, fAll a   => Free (n+1) a
  | n, fEx a    => Free (n+1) a

/-- Renamings agreeing on the free variables act equally. -/
theorem rename_ext_free (f : Form) :
    ∀ r r', (∀ n, Free n f → r n = r' n) → rename r f = rename r' f := by
  induction f with
  | fMem i j =>
    intro r r' h
    simp [rename, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fEq i j =>
    intro r r' h
    simp [rename, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fBot => intro r r' h; rfl
  | fImp a b iha ihb =>
    intro r r' h
    simp [rename, iha _ _ (fun n hn => h n (Or.inl hn)),
          ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fAnd a b iha ihb =>
    intro r r' h
    simp [rename, iha _ _ (fun n hn => h n (Or.inl hn)),
          ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fOr a b iha ihb =>
    intro r r' h
    simp [rename, iha _ _ (fun n hn => h n (Or.inl hn)),
          ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fAll a ih =>
    intro r r' h; simp [rename]
    exact ih _ _ (fun n hn => by
      cases n with
      | zero => rfl
      | succ k => simp [up, h k hn])
  | fEx a ih =>
    intro r r' h; simp [rename]
    exact ih _ _ (fun n hn => by
      cases n with
      | zero => rfl
      | succ k => simp [up, h k hn])

/-- Renamings agreeing pointwise act equally. -/
theorem rename_ext (f : Form) (r r' : Nat → Nat) (h : ∀ n, r n = r' n) :
    rename r f = rename r' f :=
  rename_ext_free f r r' (fun n _ => h n)

/-- Renaming composition. -/
theorem rename_comp (f : Form) :
    ∀ r r', rename r (rename r' f) = rename (fun n => r (r' n)) f := by
  induction f with
  | fMem i j => intro r r'; rfl
  | fEq i j => intro r r'; rfl
  | fBot => intro r r'; rfl
  | fImp a b iha ihb => intro r r'; simp [rename, iha, ihb]
  | fAnd a b iha ihb => intro r r'; simp [rename, iha, ihb]
  | fOr a b iha ihb => intro r r'; simp [rename, iha, ihb]
  | fAll a ih =>
    intro r r'; simp [rename, ih]
    exact rename_ext a _ _ (fun n => by cases n <;> simp [up])
  | fEx a ih =>
    intro r r'; simp [rename, ih]
    exact rename_ext a _ _ (fun n => by cases n <;> simp [up])

/-- Cons on renamings, and the identity `inst k ∘ up s = scons_nat k s`. -/
def scons_nat (k : Nat) (s : Nat → Nat) : Nat → Nat
  | 0 => k
  | m+1 => s m

theorem inst_up (k : Nat) (s : Nat → Nat) (n : Nat) :
    inst k (up s n) = scons_nat k s n := by
  cases n <;> rfl

theorem rename_inst_up (a : Form) (k : Nat) (s : Nat → Nat) :
    rename (inst k) (rename (up s) a) = rename (scons_nat k s) a := by
  rw [rename_comp]; exact rename_ext a _ _ (inst_up k s)

/-- Pushing a renaming `r` past an instantiation `inst k`: normalizes the
quantifier and equality-elimination cases of `Prov_rename`. -/
theorem rename_inst_push (a : Form) (r : Nat → Nat) (k : Nat) :
    rename r (rename (inst k) a) = rename (inst (r k)) (rename (up r) a) := by
  rw [rename_comp, rename_comp]
  exact rename_ext a _ _ (fun n => by cases n <;> rfl)

theorem rename_id (a : Form) : rename (fun n => n) a = a := by
  induction a with
  | fMem i j => rfl
  | fEq i j => rfl
  | fBot => rfl
  | fImp a b iha ihb => simp [rename, iha, ihb]
  | fAnd a b iha ihb => simp [rename, iha, ihb]
  | fOr a b iha ihb => simp [rename, iha, ihb]
  | fAll a ih =>
    simp [rename]
    calc rename (up fun n => n) a = rename (fun n => n) a :=
          rename_ext a _ _ (fun n => by cases n <;> rfl)
      _ = a := ih
  | fEx a ih =>
    simp [rename]
    calc rename (up fun n => n) a = rename (fun n => n) a :=
          rename_ext a _ _ (fun n => by cases n <;> rfl)
      _ = a := ih

/-! ## Bounds on free variables, sentences, sealing -/

def bound : Form → Nat
  | fMem i j => (i+1) + (j+1)
  | fEq i j  => (i+1) + (j+1)
  | fBot     => 0
  | fImp a b => bound a + bound b
  | fAnd a b => bound a + bound b
  | fOr a b  => bound a + bound b
  | fAll a   => bound a
  | fEx a    => bound a

theorem free_lt_bound (f : Form) : ∀ n, Free n f → n < bound f := by
  induction f with
  | fMem i j => intro n hn; rcases hn with rfl | rfl <;> simp [bound] <;> omega
  | fEq i j => intro n hn; rcases hn with rfl | rfl <;> simp [bound] <;> omega
  | fBot => intro n hn; cases hn
  | fImp a b iha ihb =>
    intro n hn
    rcases hn with hn | hn
    · have := iha n hn; simp [bound]; omega
    · have := ihb n hn; simp [bound]; omega
  | fAnd a b iha ihb =>
    intro n hn
    rcases hn with hn | hn
    · have := iha n hn; simp [bound]; omega
    · have := ihb n hn; simp [bound]; omega
  | fOr a b iha ihb =>
    intro n hn
    rcases hn with hn | hn
    · have := iha n hn; simp [bound]; omega
    · have := ihb n hn; simp [bound]; omega
  | fAll a ih =>
    intro n hn; have := ih (n+1) hn; simp [bound]; omega
  | fEx a ih =>
    intro n hn; have := ih (n+1) hn; simp [bound]; omega

def lmax : List Nat → Nat
  | [] => 0
  | x :: r => max x (lmax r)

theorem le_lmax {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ lmax l := by
  intro l h
  induction l with
  | nil => cases h
  | cons y r ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [lmax]; omega
    · have := ih h'; simp [lmax]; omega

def freshFor (L : List Form) : Nat := lmax (L.map bound)

theorem freshFor_not_free {L : List Form} {f : Form} (hin : f ∈ L) :
    ¬ Free (freshFor L) f := by
  intro hfree
  have h1 := free_lt_bound f _ hfree
  have h2 : bound f ≤ freshFor L := le_lmax (List.mem_map_of_mem hin)
  omega

def rho_w (w : Nat) : Nat → Nat := fun n => if n = w then 0 else n + 1

theorem rho_inst (a : Form) (w : Nat) (hfree : ¬ Free (w+1) a) :
    rename (rho_w w) (rename (inst w) a) = a := by
  rw [rename_comp]
  rw [rename_ext_free a (fun n => rho_w w (inst w n)) (fun n => n) ?_]
  · exact rename_id a
  · intro n hn
    cases n with
    | zero => simp [inst, rho_w]
    | succ m =>
      simp only [inst, rho_w]
      by_cases hmw : m = w
      · subst hmw; exact absurd hn hfree
      · simp [hmw]

theorem rho_under (a : Form) (w : Nat) (hfree : ¬ Free (w+1) a) :
    rename (up (rho_w w)) a = rename (up Nat.succ) a := by
  apply rename_ext_free
  intro n hn
  cases n with
  | zero => rfl
  | succ m =>
    simp only [up, rho_w]
    by_cases hmw : m = w
    · subst hmw; exact absurd hn hfree
    · simp [hmw, Nat.succ_eq_add_one]

theorem map_rho_S (G : List Form) (w : Nat) (h : ∀ g ∈ G, ¬ Free w g) :
    G.map (rename (rho_w w)) = G.map (rename Nat.succ) := by
  apply List.map_congr_left
  intro g hg
  apply rename_ext_free
  intro n hn
  simp only [rho_w]
  by_cases hnw : n = w
  · subst hnw; exact absurd hn (h g hg)
  · simp [hnw, Nat.succ_eq_add_one]

def Sentence (f : Form) : Prop := ∀ n, ¬ Free n f

def Sentences (B : Form → Prop) : Prop := ∀ f, B f → Sentence f

/-- A sentence is invariant under every variable renaming.  Keeping this at
the formula layer avoids reproving the same closed-formula fact in each
theory-specific translation. -/
theorem rename_eq_of_sentence (f : Form) (hf : Sentence f) (r : Nat → Nat) :
    rename r f = f := by
  rw [rename_ext_free f r (fun n => n) (fun n hn => (hf n hn).elim)]
  exact rename_id f

def closeN : Nat → Form → Form
  | 0, f => f
  | k+1, f => closeN k (fAll f)

theorem Free_closeN : ∀ (k : Nat) (f : Form) (n : Nat),
    Free n (closeN k f) → Free (k + n) f := by
  intro k
  induction k with
  | zero => intro f n h; rw [Nat.zero_add]; exact h
  | succ k ih =>
    intro f n h
    have h1 : Free (k + n) (fAll f) := ih (fAll f) n h
    have h2 : Free (k + n + 1) f := h1
    have harg : k + 1 + n = k + n + 1 := by omega
    rw [harg]; exact h2

/-- Universal closure of a formula (Coq: `seal`; `seal` is a Lean keyword). -/
def sealF (f : Form) : Form := closeN (bound f) f

theorem Sentence_seal (f : Form) : Sentence (sealF f) := by
  intro n h
  have h1 := Free_closeN (bound f) f n h
  have h2 := free_lt_bound f _ h1
  omega

/-! ## Enumeration of formulas (Cantor pairing) -/

def code : Form → Nat
  | fMem i j => Cantor.toNat (0, Cantor.toNat (i, j))
  | fEq i j  => Cantor.toNat (1, Cantor.toNat (i, j))
  | fBot     => Cantor.toNat (2, 0)
  | fImp a b => Cantor.toNat (3, Cantor.toNat (code a, code b))
  | fAnd a b => Cantor.toNat (4, Cantor.toNat (code a, code b))
  | fOr a b  => Cantor.toNat (5, Cantor.toNat (code a, code b))
  | fAll a   => Cantor.toNat (6, code a)
  | fEx a    => Cantor.toNat (7, code a)

def decode : Nat → Nat → Form
  | 0, _ => fBot
  | fuel+1, n =>
    let p := (Cantor.ofNat n).2
    match (Cantor.ofNat n).1 with
    | 0 => fMem (Cantor.ofNat p).1 (Cantor.ofNat p).2
    | 1 => fEq (Cantor.ofNat p).1 (Cantor.ofNat p).2
    | 2 => fBot
    | 3 => fImp (decode fuel (Cantor.ofNat p).1) (decode fuel (Cantor.ofNat p).2)
    | 4 => fAnd (decode fuel (Cantor.ofNat p).1) (decode fuel (Cantor.ofNat p).2)
    | 5 => fOr (decode fuel (Cantor.ofNat p).1) (decode fuel (Cantor.ofNat p).2)
    | 6 => fAll (decode fuel p)
    | 7 => fEx (decode fuel p)
    | _+8 => fBot

theorem decode_code (f : Form) : ∀ fuel, code f < fuel → decode fuel (code f) = f := by
  induction f with
  | fMem i j =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 => simp [code, decode, Cantor.ofNat_toNat]
  | fEq i j =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 => simp [code, decode, Cantor.ofNat_toNat]
  | fBot =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 => simp [code, decode, Cantor.ofNat_toNat]
  | fImp a b iha ihb =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 =>
      have b1 := Cantor.add_le_toNat 3 (Cantor.toNat (code a, code b))
      have b2 := Cantor.add_le_toNat (code a) (code b)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat,
            iha fuel (by omega), ihb fuel (by omega)]
  | fAnd a b iha ihb =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 =>
      have b1 := Cantor.add_le_toNat 4 (Cantor.toNat (code a, code b))
      have b2 := Cantor.add_le_toNat (code a) (code b)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat,
            iha fuel (by omega), ihb fuel (by omega)]
  | fOr a b iha ihb =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 =>
      have b1 := Cantor.add_le_toNat 5 (Cantor.toNat (code a, code b))
      have b2 := Cantor.add_le_toNat (code a) (code b)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat,
            iha fuel (by omega), ihb fuel (by omega)]
  | fAll a ih =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 =>
      have b1 := Cantor.add_le_toNat 6 (code a)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat, ih fuel (by omega)]
  | fEx a ih =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel+1 =>
      have b1 := Cantor.add_le_toNat 7 (code a)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat, ih fuel (by omega)]

def Enum (n : Nat) : Form := decode (n+1) n

theorem Enum_surj (f : Form) : ∃ n, Enum n = f :=
  ⟨code f, decode_code f (code f + 1) (by omega)⟩

/-! ## Tarski semantics over a structure -/

section Semantics

universe u
variable {V : Type u}

def Sub (mem : V → V → Prop) (a b : V) : Prop := ∀ x, mem x a → mem x b

def scons (d : V) (e : Nat → V) : Nat → V
  | 0 => d
  | k+1 => e k

def Sat (mem : V → V → Prop) : (Nat → V) → Form → Prop
  | e, fMem i j => mem (e i) (e j)
  | e, fEq i j  => e i = e j
  | _, fBot     => False
  | e, fImp a b => Sat mem e a → Sat mem e b
  | e, fAnd a b => Sat mem e a ∧ Sat mem e b
  | e, fOr a b  => Sat mem e a ∨ Sat mem e b
  | e, fAll a   => ∀ d, Sat mem (scons d e) a
  | e, fEx a    => ∃ d, Sat mem (scons d e) a

variable {mem : V → V → Prop}

/-- Satisfaction of `fIff` is a genuine iff. -/
theorem Sat_fIff {e : Nat → V} {a b : Form} :
    Sat mem e (fIff a b) ↔ (Sat mem e a ↔ Sat mem e b) := by
  show (Sat mem e a → Sat mem e b) ∧ (Sat mem e b → Sat mem e a) ↔ _
  constructor
  · intro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · intro h; exact ⟨h.mp, h.mpr⟩

/-! ### Satisfaction depends only on the free variables -/

theorem Sat_ext_free (f : Form) :
    ∀ e1 e2 : Nat → V, (∀ n, Free n f → e1 n = e2 n) →
      (Sat mem e1 f ↔ Sat mem e2 f) := by
  induction f with
  | fMem i j =>
    intro e1 e2 h
    simp [Sat, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fEq i j =>
    intro e1 e2 h
    simp [Sat, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fBot => intro e1 e2 h; simp [Sat]
  | fImp a b iha ihb =>
    intro e1 e2 h; simp only [Sat]
    rw [iha _ _ (fun n hn => h n (Or.inl hn)), ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fAnd a b iha ihb =>
    intro e1 e2 h; simp only [Sat]
    rw [iha _ _ (fun n hn => h n (Or.inl hn)), ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fOr a b iha ihb =>
    intro e1 e2 h; simp only [Sat]
    rw [iha _ _ (fun n hn => h n (Or.inl hn)), ihb _ _ (fun n hn => h n (Or.inr hn))]
  | fAll a ih =>
    intro e1 e2 h; simp only [Sat]
    refine forall_congr' fun d => ih _ _ (fun n hn => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [scons]; exact h m hn
  | fEx a ih =>
    intro e1 e2 h; simp only [Sat]
    refine exists_congr fun d => ih _ _ (fun n hn => ?_)
    cases n with
    | zero => rfl
    | succ m => simp only [scons]; exact h m hn

/-- Satisfaction respects pointwise-equal environments. -/
theorem Sat_ext (f : Form) (e1 e2 : Nat → V) (h : ∀ n, e1 n = e2 n) :
    Sat mem e1 f ↔ Sat mem e2 f :=
  Sat_ext_free f e1 e2 (fun n _ => h n)

theorem up_env (r : Nat → Nat) (d : V) (e : Nat → V) (n : Nat) :
    scons d e (up r n) = scons d (fun m => e (r m)) n := by
  cases n <;> rfl

theorem Sat_rename (f : Form) :
    ∀ (r : Nat → Nat) (e : Nat → V),
      Sat mem e (rename r f) ↔ Sat mem (fun n => e (r n)) f := by
  induction f with
  | fMem i j => intro r e; simp [Sat, rename]
  | fEq i j => intro r e; simp [Sat, rename]
  | fBot => intro r e; simp [Sat, rename]
  | fImp a b iha ihb =>
    intro r e; simp only [Sat, rename]
    rw [iha, ihb]
  | fAnd a b iha ihb =>
    intro r e; simp only [Sat, rename]
    rw [iha, ihb]
  | fOr a b iha ihb =>
    intro r e; simp only [Sat, rename]
    rw [iha, ihb]
  | fAll a ih =>
    intro r e; simp only [Sat, rename]
    refine forall_congr' fun d => ?_
    rw [ih]
    exact Sat_ext a _ _ (up_env r d e)
  | fEx a ih =>
    intro r e; simp only [Sat, rename]
    refine exists_congr fun d => ?_
    rw [ih]
    exact Sat_ext a _ _ (up_env r d e)

/-- Renaming followed by a pointwise environment identification.

This is the common semantic transport step for instantiation and binder
bookkeeping: clients can state the intended target environment directly
instead of chaining `Sat_rename` and `Sat_ext` by hand. -/
theorem Sat_rename_ext (f : Form) (r : Nat → Nat) (e e' : Nat → V)
    (h : ∀ n, e (r n) = e' n) :
    Sat mem e (rename r f) ↔ Sat mem e' f := by
  rw [Sat_rename]
  exact Sat_ext f _ _ h

/-- Environment lemma for the quantifier/equality cases. -/
theorem inst_env (k : Nat) (e : Nat → V) (n : Nat) :
    e (inst k n) = scons (e k) e n := by
  cases n <;> rfl

/-- Relation defined by a formula `psi` with vars 0,1 the two arguments. -/
def relOf (mem : V → V → Prop) (psi : Form) (e : Nat → V) : V → V → Prop :=
  fun z x => Sat mem (scons z (scons x e)) psi

/-- A renamed relation formula denotes `relOf` whenever its environment agrees
pointwise with the relation's two distinguished arguments and parameters. -/
theorem Sat_rename_relOf (psi : Form) (r : Nat → Nat) (env e : Nat → V)
    (z x : V) (h : ∀ n, env (r n) = scons z (scons x e) n) :
    Sat mem env (rename r psi) ↔ relOf mem psi e z x := by
  unfold relOf
  exact Sat_rename_ext psi r env _ h

def SetLike (mem : V → V → Prop) (R : V → V → Prop) : Prop :=
  ∀ x, ∃ y, ∀ z, R z x → mem z y

def Functional (R : V → V → Prop) : Prop :=
  ∀ x y1 y2, R y1 x → R y2 x → y1 = y2

end Semantics

/-! ## Sealing is semantically transparent; extraction -/

section Sealing

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem closeN_valid (k : Nat) :
    ∀ g : Form, (∀ e : Nat → V, Sat mem e (closeN k g)) ↔ (∀ e, Sat mem e g) := by
  induction k with
  | zero => intro g; exact Iff.rfl
  | succ k ih =>
    intro g
    show (∀ e, Sat mem e (closeN k (fAll g))) ↔ _
    rw [ih (fAll g)]
    constructor
    · intro h e'
      have pf : ∀ n, scons (e' 0) (fun n => e' (n+1)) n = e' n := by
        intro n; cases n <;> rfl
      exact (Sat_ext g _ _ pf).mp (h (fun n => e' (n+1)) (e' 0))
    · intro h e d; exact h _

theorem seal_valid (g : Form) :
    (∀ e : Nat → V, Sat mem e (sealF g)) ↔ (∀ e, Sat mem e g) :=
  closeN_valid (bound g) g

theorem Sat_sentence_inv (g : Form) (hg : Sentence g) (v1 v2 : Nat → V) :
    Sat mem v1 g ↔ Sat mem v2 g :=
  Sat_ext_free g v1 v2 (fun n hn => absurd hn (hg n))

/-- Extract a universal instance of a sealed axiom from a model of a theory. -/
theorem extract (B : Form → Prop) (v : Nat → V) (g : Form)
    (hT : ∀ g', B g' → Sat mem v g') (hin : B (sealF g)) :
    ∀ e, Sat mem e g := by
  rw [← closeN_valid (bound g) g]
  intro e'
  exact (Sat_sentence_inv (sealF g) (Sentence_seal g) v e').mp (hT _ hin)

end Sealing

end SetTheory
