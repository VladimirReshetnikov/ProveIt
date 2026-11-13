import ZFCinPA.EnvTransform

set_option autoImplicit false
noncomputable section

/-!
# Pure pieces of the reflection templates

The templates of the `hSchema` generator speak about constructible stages,
their membership relations, internal environments and internal satisfaction.
Each such notion is a fixed set-theoretic semisentence, obtained from a named
formula of `BusyBeaver.ZFC` or `BoundedZFCConsistency` (`piece`), together with
its evaluation in every model of ZF (`eval_*`):

| piece      | arity | meaning                                         |
| ---------- | ----- | ----------------------------------------------- |
| `ordP`     | 1     | `β` is an ordinal                               |
| `limP`     | 1     | `β` is a nonzero limit ordinal                  |
| `stageP`   | 2     | `S = L_β`                                       |
| `memRelP`  | 2     | `R` is the membership relation of `S`           |
| `envP`     | 2     | `t` is an internal environment over `S`         |
| `finSuppP` | 1     | `t` is eventually `∅`                           |
| `codeP`    | 1     | `c` is an internal formula code                 |
| `satP`     | 4     | `(S, R) ⊨ c[t]` (`InternalSatTotality.SatIn`)   |

and the two pieces of `EnvTransform`'s quantifier clause (`econsP`, `domYP`).
-/

namespace LeanProofs.ZFCinPA.LPieces

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ConstructibleInterpretation LeanProofs.ZFCinPA.EnvTransform

/-! ## Named formulas as semisentences -/

section Pieces

open SetTheory.BusyBeaver.ZFC.NamedZF

theorem eval_piece {V : Type*} [SetStructure V] (n : ℕ) (φ : NForm)
    (e : Fin (n + 1) → V) (ε : Empty → V) :
    (piece n φ).Eval e ε ↔
      NSat (memRel V) (fun i => if h : i < n + 1 then e ⟨i, h⟩ else e 0) φ := by
  rw [piece, Semiformula.eval_rewrite]
  have hf : (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty (n + 1)).val e ε) = fun _ => e 0 := by
    funext; simp
  rw [hf]
  refine (eval_toSet (toForm id φ) (n + 1) e (fun _ => e 0)
    (fun i => if h : i < n + 1 then e ⟨i, h⟩ else e 0)
    (fun i => by rw [dif_pos i.isLt]) (fun j => by rw [dif_neg (by omega)])).trans ?_
  exact sat_toForm _ φ id _

/-- `a` is a nonzero limit ordinal. -/
def limF (a : ℕ) : NForm :=
  .and (SetTheory.BusyBeaver.ZFC.InternalOrd.ordF a)
    (.and (.ex (a + 1) (.mem (a + 1) a))
      (.all (a + 1) (.imp (.mem (a + 1) a) (.ex (a + 2) (.and (.mem (a + 2) a) (.mem (a + 1) (a + 2)))))))

/-- `t` is eventually `∅` (names: `t = 0`, `k = 1`, `i = 2`, `z = 3`, `w = 4`). -/
def finSuppF : NForm :=
  .ex 1 (.and (.atom (BoundedZFCConsistency.fNatF 0) (SetTheory.BusyBeaver.ZFC.ConstructibleDef.argsOf [1]))
    (.all 2 (.imp (.and (.atom (BoundedZFCConsistency.fNatF 0)
        (SetTheory.BusyBeaver.ZFC.ConstructibleDef.argsOf [2])) (.or (.mem 1 2) (.eq 1 2)))
      (.all 3 (.imp (SetTheory.BusyBeaver.ZFC.InternalRank.pmemF 0 2 3)
        (.all 4 (.imp (.mem 4 3) .bot)))))))

end Pieces

def ordP : SetTheorySemisentence 1 := piece 0 (SetTheory.BusyBeaver.ZFC.InternalOrd.ordF 0)
def limP : SetTheorySemisentence 1 := piece 0 (limF 0)
def stageP : SetTheorySemisentence 2 := piece 1 (isStageLF 0 1)
def memRelP : SetTheorySemisentence 2 := piece 1 (SetTheory.BusyBeaver.ZFC.ConstructibleDef.memRelF 1 0)
def envP : SetTheorySemisentence 2 := piece 1 (SetTheory.BusyBeaver.ZFC.ConstructibleDef.envOnF 1 0)
def finSuppP : SetTheorySemisentence 1 := piece 0 finSuppF
def codeP : SetTheorySemisentence 1 := piece 0 (SetTheory.BusyBeaver.ZFC.ConstructibleDef.isCodeF 0)
def satP : SetTheorySemisentence 4 := piece 3 (SetTheory.BusyBeaver.ZFC.ConstructibleDef.satInF 0 1 2 3)

/-! ## Semantics -/

section Semantics

open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.NamedZF
  SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.InternalRank
  SetTheory.BusyBeaver.ZFC.ConstructibleDef SetTheory.BusyBeaver.ZFC.Constructible
  LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V]

/-- `β` is a nonzero limit ordinal. -/
def IsLim (mem : V → V → Prop) (β : V) : Prop :=
  Ord mem β ∧ (∃ x, mem x β) ∧ ∀ α, mem α β → ∃ γ, mem γ β ∧ mem α γ

/-- `t` is eventually `∅`. -/
def FinSupp (H : _root_.SetTheory.ZFAxioms (memRel V)) (t : V) : Prop :=
  ∃ k, memRel V k (_root_.SetTheory.omegaV H) ∧ ∀ i, memRel V i (_root_.SetTheory.omegaV H) →
    (memRel V k i ∨ k = i) → ∀ z, memRel V (_root_.SetTheory.kpair H i z) t → ∀ w, ¬ memRel V w z

variable (ε : Empty → V)

@[simp] theorem eval_ordP (β : V) : ordP.Eval ![β] ε ↔ Ord (memRel V) β := by
  rw [ordP, eval_piece]
  simp [nsat_ordF]

@[simp] theorem eval_limP (β : V) : limP.Eval ![β] ε ↔ IsLim (memRel V) β := by
  rw [limP, eval_piece]
  simp only [limF, NSat, nsat_ordF]
  simp (disch := omega) only [upd_same, upd_other]
  simp [IsLim]

variable (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

/-- The model-independent stage formula is BusyBeaver's at `Gdef`. -/
theorem isStageLF_eq (a S : ℕ) : isStageLF a S = TransRec.isStageF (defOp H hP) a S := rfl

@[simp] theorem eval_stageP (β S : V) :
    stageP.Eval ![β, S] ε ↔ IsL H hP β S := by
  rw [stageP, eval_piece, isStageLF_eq H hP]
  rw [TransRec.nsat_isStageF H (defOp H hP)]
  rfl

@[simp] theorem eval_memRelP (S R : V) :
    memRelP.Eval ![S, R] ε ↔ MemRel H S R := by
  rw [memRelP, eval_piece, nsat_memRelF H]
  rfl

@[simp] theorem eval_envP (S t : V) :
    envP.Eval ![S, t] ε ↔ IsEnvOn H S t := by
  rw [envP, eval_piece, nsat_envOnF H]
  rfl

@[simp] theorem eval_finSuppP (t : V) :
    finSuppP.Eval ![t] ε ↔ FinSupp H t := by
  rw [finSuppP, eval_piece]
  simp only [finSuppF, NSat, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  simp only [argsOf, fNatF_spec H]
  simp [FinSupp, upd]

@[simp] theorem eval_codeP (c : V) :
    codeP.Eval ![c] ε ↔ IsFormCodeSem H c := by
  rw [codeP, eval_piece, nsat_isCodeF H]
  rfl

@[simp] theorem eval_satP (A R c t : V) :
    satP.Eval ![A, R, c, t] ε ↔ LeanProofs.BoundedZFCConsistency.SatIn H A R c t := by
  rw [satP, eval_piece, nsat_satInF H]
  rfl

end Semantics

end LeanProofs.ZFCinPA.LPieces
