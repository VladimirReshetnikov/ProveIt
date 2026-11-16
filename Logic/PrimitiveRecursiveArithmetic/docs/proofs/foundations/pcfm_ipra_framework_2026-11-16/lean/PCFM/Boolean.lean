import IPRADerivations.Core.Pairing

/-!
# Boolean terms and the QF-reflection interface

This file contains the data layer and exact target signatures.  The recursive
proof-producing compiler is intentionally not postulated as an axiom; it is
the first substantive implementation milestone described in the paper.
-/

namespace LeanProofs.IPRA.Framework

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ}

/-- The numeral one in the current term scope. -/
abbrev oneT : PTm n := succ zero

/-- Internal Booleanity. -/
def IsBool (b : PTm n) : Fm PTm n :=
  (b ≐ zero) ⋎ (b ≐ oneT)

/-- Boolean negation on Boolean inputs. -/
def bnot (b : PTm n) : PTm n := monus oneT b

/-- Boolean conjunction on Boolean inputs. -/
def band (b c : PTm n) : PTm n := b * c

/-- Boolean disjunction on Boolean inputs. -/
def bor (b c : PTm n) : PTm n :=
  monus oneT (bnot b * bnot c)

/-- Boolean implication on Boolean inputs. -/
def bimp (b c : PTm n) : PTm n := bor (bnot b) c

@[simp] theorem subst_IsBool {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    (IsBool b).subst σ = IsBool (Syn.subst σ b) := by
  simp [IsBool, oneT]

@[simp] theorem subst_bnot {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    Syn.subst σ (bnot b) = bnot (Syn.subst σ b) := by
  simp [bnot, oneT]

@[simp] theorem subst_band {m : ℕ} (σ : Fin n → PTm m) (b c : PTm n) :
    Syn.subst σ (band b c) = band (Syn.subst σ b) (Syn.subst σ c) := by
  simp [band]

@[simp] theorem subst_bor {m : ℕ} (σ : Fin n → PTm m) (b c : PTm n) :
    Syn.subst σ (bor b c) = bor (Syn.subst σ b) (Syn.subst σ c) := by
  simp [bor]

@[simp] theorem subst_bimp {m : ℕ} (σ : Fin n → PTm m) (b c : PTm n) :
    Syn.subst σ (bimp b c) = bimp (Syn.subst σ b) (Syn.subst σ c) := by
  simp [bimp]

/-- Target payload of the quantifier-free reflection compiler. -/
structure ReflectedQF (φ : Fm PTm n) where
  bit : PTm n
  bool : ([] : List (Fm PTm n)) ⊢[PRAAx] IsBool bit
  trueIff :
    ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff φ (bit ≐ oneT)
  falseIff :
    ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (φ ⟶ Fm.bot) (bit ≐ zero)

/-
Planned theorem, implemented by structural recursion on `φ` and `hφ`:

def reflectQF (φ : Fm PTm n) (hφ : φ.QF) : ReflectedQF φ

Required cases:
* equality: `eqb`, `eqb_of_eq`, `eqb_of_ne`, `eq_or_ne`;
* falsity: bit `0`;
* and/or/imp: `band`/`bor`/`bimp` plus finite Boolean case analysis;
* all/ex: impossible from `hφ`.

No opaque `reflect` constant or semantic axiom should be introduced.
-/

end LeanProofs.IPRA.Framework
