import BusyBeaver.ZFC.TransRec
import BoundedZFCConsistency.InternalSatTotality

/-!
Definable subsets of a set, inside a model of ZF.

For a set `X` of the model, `MemRel X R` says that `R` is the membership
relation of `X` as a set of Kuratowski pairs, and `DefinableIn X S` says that
`S = {y ∈ X | (X, ∈) ⊨ φ[y, e]}` for some internal formula code `φ` and some
internal environment `e` over `X`. Satisfaction is
`BoundedZFCConsistency.InternalSatTotality.SatIn`: satisfaction of coded
formulas over set-sized structures, by certificates, total and single-valued
on every internal code (including nonstandard ones).

`Gdef X = {S ⊆ X | S = ∅ or S is definable over X}` is a definable operation
(`defOp`); its stages (`TransRec`) form Gödel's constructible hierarchy. The
empty set is added so that `Gdef ∅ = {∅}`: with an empty carrier there is no
environment, so nothing would otherwise be definable over `∅`.
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleDef

open NamedZF NForm InternalOrd InternalRank TransRec LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Read slot `i` of an embedded De Bruijn formula at the `i`-th listed name. -/
def argsOf (l : List Nat) (i : Nat) : Nat := l.getD i 0

/-! ## The membership relation of a set -/

def MemRel (H : ZFAxioms mem) (X R : V) : Prop :=
  ∀ p, mem p R ↔ ∃ a b, mem a X ∧ mem b X ∧ mem a b ∧ p = kpair H a b

def memRelF (R X : Nat) : NForm :=
  let n := R + X + 1
  .all n ((NForm.mem n R).iff (.ex (n + 1) (.ex (n + 2) (.and (.mem (n + 1) X)
    (.and (.mem (n + 2) X) (.and (.mem (n + 1) (n + 2)) (kpairF n (n + 1) (n + 2))))))))

theorem nsat_memRelF (H : ZFAxioms mem) (ρ : Nat → V) (R X : Nat) :
    NSat mem ρ (memRelF R X) ↔ MemRel H (ρ X) (ρ R) := by
  simp only [memRelF, NSat, nsat_iff, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

theorem memRel_exists (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (X : V) :
    ∃ R, MemRel H X R := by
  obtain ⟨P1, hP1⟩ := hP X
  obtain ⟨P2, hP2⟩ := hP P1
  obtain ⟨R, hR⟩ := sep_of H (fun p => ∃ a b, mem a X ∧ mem b X ∧ mem a b ∧ p = kpair H a b)
    (.ex 1 (.ex 2 (.and (.mem 1 3) (.and (.mem 2 3) (.and (.mem 1 2) (kpairF 0 1 2))))))
    (fun _ => X)
    (fun p => by
      simp only [NSat, nsat_kpairF H]
      simp (disch := omega) only [upd_same, upd_other]) P2
  refine ⟨R, fun p => ?_⟩
  rw [hR p]
  refine ⟨fun h => h.2, ?_⟩
  rintro ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨(hP2 _).2 fun q hq => (hP1 q).2 ?_, a, b, ha, hb, hab, rfl⟩
  rcases (kpair_mem H a b q).1 hq with rfl | rfl
  · intro z hz; rwa [(vsingle_spec H a z).1 hz]
  · intro z hz; rcases (vpair_spec H a b z).1 hz with rfl | rfl <;> assumption

/-! ## Internal satisfaction as a named formula -/

/-- `b = 1` (the internal numeral `{∅}`). -/
def oneF (b : Nat) : NForm :=
  .all (b + 1) ((NForm.mem (b + 1) b).iff (.all (b + 2) (.imp (.mem (b + 2) (b + 1)) .bot)))

theorem nsat_oneF (H : ZFAxioms mem) (ρ : Nat → V) (b : Nat) :
    NSat mem ρ (oneF b) ↔ ρ b = natV H 1 := by
  simp only [oneF, NSat, nsat_iff]
  simp (disch := omega) only [upd_same, upd_other]
  have hz : ∀ z, (∀ m, ¬ mem m z) ↔ z = vempty H := fun z =>
    ⟨fun h => H.ext _ _ fun m => ⟨fun hm => absurd hm (h m), fun hm => absurd hm (vempty_spec H m)⟩,
     fun h m hm => vempty_spec H m (h ▸ hm)⟩
  have h1 : ∀ z, mem z (natV H 1) ↔ z = vempty H := fun z => by
    rw [natV_succ, natV_zero, vsucc_spec H (vempty H) z]
    exact ⟨fun h => h.elim (fun h => absurd h (vempty_spec H z)) id, Or.inr⟩
  exact ⟨fun h => H.ext _ _ fun z => by rw [h z, hz, h1], fun h z => by rw [h, h1, hz]⟩

/-! ### Embedded certificate formulas -/

def isCodeF (c : Nat) : NForm := .atom (fIsFormCodeF 0) (argsOf [c])
def envOnF (e A : Nat) : NForm := .atom (fEnvOnF 0 1) (argsOf [e, A])
def satClosedF (S A R : Nat) : NForm := .atom (fSatClosedF 0 1 2) (argsOf [S, A, R])
def tripleMemF (c e b S : Nat) : NForm := .atom (fTripleMemF 0 1 2 3) (argsOf [c, e, b, S])
def econsAtomF (z d E : Nat) : NForm := .atom (fEconsF 0 1 2) (argsOf [z, d, E])

theorem nsat_isCodeF (H : ZFAxioms mem) (ρ : Nat → V) (c : Nat) :
    NSat mem ρ (isCodeF c) ↔ IsFormCodeSem H (ρ c) := by
  simp only [isCodeF, NSat]; rw [fIsFormCodeF_spec H]; rfl

theorem nsat_envOnF (H : ZFAxioms mem) (ρ : Nat → V) (e A : Nat) :
    NSat mem ρ (envOnF e A) ↔ IsEnvOn H (ρ A) (ρ e) := by
  simp only [envOnF, NSat]; rw [fEnvOnF_spec H]; rfl

theorem nsat_satClosedF (H : ZFAxioms mem) (ρ : Nat → V) (S A R : Nat) :
    NSat mem ρ (satClosedF S A R) ↔ SatClosed H (ρ A) (ρ R) (ρ S) := by
  simp only [satClosedF, NSat]; rw [fSatClosedF_spec H]; rfl

theorem nsat_tripleMemF (H : ZFAxioms mem) (ρ : Nat → V) (c e b S : Nat) :
    NSat mem ρ (tripleMemF c e b S) ↔ mem (satTriple H (ρ c) (ρ e) (ρ b)) (ρ S) := by
  simp only [tripleMemF, NSat]; rw [fTripleMemF_spec H]; rfl

theorem nsat_econsAtomF (H : ZFAxioms mem) (ρ : Nat → V) (z d E : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ρ E) → mem (kpair H x y') (ρ E) → y = y') :
    NSat mem ρ (econsAtomF z d E) ↔ ρ z = econs H (ρ d) (ρ E) := by
  simp only [econsAtomF, NSat]; rw [fEconsF_spec H _ 0 1 2 hfun]; rfl

/-- `(A, R) ⊨ c[e]` (internal satisfaction). -/
def satInF (A R c e : Nat) : NForm :=
  let n := A + R + c + e + 1
  .ex n (.ex (n + 1) (.and (oneF (n + 1)) (.and (satClosedF n A R) (tripleMemF c e (n + 1) n))))

theorem nsat_satInF (H : ZFAxioms mem) (ρ : Nat → V) (A R c e : Nat) :
    NSat mem ρ (satInF A R c e) ↔ SatIn H (ρ A) (ρ R) (ρ c) (ρ e) := by
  simp only [satInF, NSat, nsat_oneF H, nsat_satClosedF H, nsat_tripleMemF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨S, _, rfl, hc, hh⟩ => ⟨S, hc, hh⟩, fun ⟨S, hc, hh⟩ => ⟨S, _, rfl, hc, hh⟩⟩

/-! ## Definable subsets -/

/-- `S` is a subset of `X` definable over `(X, ∈)` with parameters from `X`. -/
def DefinableIn (H : ZFAxioms mem) (X S : V) : Prop :=
  ∃ R c e, MemRel H X R ∧ IsFormCodeSem H c ∧ IsEnvOn H X e ∧
    ∀ y, mem y S ↔ mem y X ∧ SatIn H X R c (econs H y e)

def definableF (X S : Nat) : NForm :=
  let n := X + S + 1
  .ex n (.ex (n + 1) (.ex (n + 2) (.and (memRelF n X) (.and (isCodeF (n + 1))
    (.and (envOnF (n + 2) X)
    (.all (n + 3) ((NForm.mem (n + 3) S).iff (.and (.mem (n + 3) X)
      (.ex (n + 4) (.and (econsAtomF (n + 4) (n + 3) (n + 2)) (satInF X n (n + 1) (n + 4))))))))))))

theorem nsat_definableF (H : ZFAxioms mem) (ρ : Nat → V) (X S : Nat) :
    NSat mem ρ (definableF X S) ↔ DefinableIn H (ρ X) (ρ S) := by
  simp only [definableF, NSat, nsat_iff, nsat_memRelF H, nsat_satInF H, nsat_isCodeF H,
    nsat_envOnF H]
  simp (disch := omega) only [upd_same, upd_other]
  refine exists_congr fun R => exists_congr fun c => exists_congr fun e => ?_
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hE => ?_
  refine forall_congr' fun y => iff_congr Iff.rfl (and_congr_right fun _ => ?_)
  have key : ∀ e', NSat mem (upd (upd (upd (upd (upd ρ (X + S + 1) R) (X + S + 1 + 1) c)
      (X + S + 1 + 2) e) (X + S + 1 + 3) y) (X + S + 1 + 4) e')
      (econsAtomF (X + S + 1 + 4) (X + S + 1 + 3) (X + S + 1 + 2)) ↔ e' = econs H y e := by
    intro e'
    rw [nsat_econsAtomF H _ _ _ _ (by simp (disch := omega) only [upd_same, upd_other]; exact hE.1.1)]
    simp (disch := omega) only [upd_same, upd_other]
  refine ⟨fun ⟨e', he', hs⟩ => ?_, fun hs => ⟨_, (key _).2 rfl, hs⟩⟩
  rwa [(key e').1 he'] at hs

/-! ## The stage operation -/

theorem gdef_exists (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (X : V) :
    ∃ D, ∀ S, mem S D ↔ Sub mem S X ∧ ((∀ z, ¬ mem z S) ∨ DefinableIn H X S) := by
  obtain ⟨P, hPX⟩ := hP X
  obtain ⟨D, hD⟩ := sep_of H (fun S => (∀ z, ¬ mem z S) ∨ DefinableIn H X S)
    (.or (.all 2 (.imp (.mem 2 0) .bot)) (definableF 1 0)) (fun _ => X)
    (fun S => by
      simp only [NSat, nsat_definableF H]
      simp (disch := omega) only [upd_same, upd_other]) P
  exact ⟨D, fun S => by rw [hD S, hPX S]⟩

/-- `Gdef X = {S ⊆ X | S = ∅ or S is definable over X}`. -/
noncomputable def Gdef (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (X : V) : V :=
  (gdef_exists H hP X).choose

theorem gdef_spec (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (X S : V) :
    mem S (Gdef H hP X) ↔ Sub mem S X ∧ ((∀ z, ¬ mem z S) ∨ DefinableIn H X S) :=
  (gdef_exists H hP X).choose_spec S

/-- The graph of `Gdef` (output name `y`, input name `x`). -/
def gdefF (y x : Nat) : NForm :=
  let n := y + x + 1
  .all n ((NForm.mem n y).iff (.and (subF n x)
    (.or (.all (n + 1) (.imp (.mem (n + 1) n) .bot)) (definableF x n))))

/-- `Gdef` is a definable operation. -/
noncomputable def defOp (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) :
    DefOp mem (Gdef H hP) where
  gF := gdefF
  spec := fun ρ y x => by
    simp only [gdefF, NSat, nsat_iff, nsat_subF, nsat_definableF H]
    simp (disch := omega) only [upd_same, upd_other]
    constructor
    · intro h; exact H.ext _ _ fun S => by rw [h S, gdef_spec H hP]
    · intro h S; rw [h, gdef_spec H hP]

end SetTheory.BusyBeaver.ZFC.ConstructibleDef
