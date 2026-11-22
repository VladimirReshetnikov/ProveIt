import IPRADerivations.Core.Tactic

/-! Imported from the packet `analysis/quantum_ipra_2026-11-20`, `lean/QuantumIdentities.lean`: the namespace is placed under `LeanProofs.IPRA` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Polynomial identities for unnormalised complex amplitudes in the object theory.
A signed integer is a pair of natural-number terms. Rational identities follow
by clearing common positive denominators. The object sentences have no premises. -/
namespace LeanProofs.IPRA.Analysis.Quantum.Identities
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

structure Amp (n : ℕ) where
  re : ZT n
  im : ZT n

namespace Amp
variable {n : ℕ}
def plus (z w : Amp n) : Amp n := ⟨z.re + w.re, z.im + w.im⟩
def minus (z w : Amp n) : Amp n := ⟨z.re - w.re, z.im - w.im⟩
def times (z w : Amp n) : Amp n :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def star (z : Amp n) : Amp n := ⟨z.re, -z.im⟩
def weight (z : Amp n) : ZT n := ZT.sq z.re + ZT.sq z.im
def vars (a b c d : Fin n) : Amp n := ⟨ZT.var2 a b, ZT.var2 c d⟩
end Amp

open Amp
variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Sum over the bright and dark ports of a Hadamard interferometer. -/
def ports (z w : Amp n) : Fm PTm n :=
  ZT.eq (weight (plus z w) + weight (minus z w))
    ((ZT.natLit 2) * (weight z + weight w))

theorem ports_at (z w : Amp n) : Γ ⊢[PRAAx] ports z w := by
  unfold ports weight plus minus
  ipra_ring

def portsSentence : Fm PTm 0 := univ 8 (ports (vars 0 1 2 3) (vars 4 5 6 7))
theorem ports_closed : [] ⊢[PRAAx] portsSentence := closeUniv 8 (ports_at _ _)

/-- Squared norm of an unnormalised SU(2) matrix acting on a spinor. -/
def spin (a b z w : Amp n) : Fm PTm n :=
  ZT.eq (weight (minus (times a z) (times (Amp.star b) w)) +
         weight (plus (times b z) (times (Amp.star a) w)))
    ((weight a + weight b) * (weight z + weight w))

theorem spin_at (a b z w : Amp n) : Γ ⊢[PRAAx] spin a b z w := by
  unfold spin weight plus minus times Amp.star
  ipra_ring

def spinSentence : Fm PTm 0 := univ 16
  (spin (vars 0 1 2 3) (vars 4 5 6 7) (vars 8 9 10 11) (vars 12 13 14 15))
theorem spin_closed : [] ⊢[PRAAx] spinSentence := closeUniv 16 (spin_at _ _ _ _)

/-- Lagrange's identity, giving the slack in spinor Cauchy–Schwarz. -/
def lagrange (a b z w : Amp n) : Fm PTm n :=
  ZT.eq (weight (plus (times (Amp.star a) z) (times (Amp.star b) w)) +
         weight (minus (times a w) (times b z)))
    ((weight a + weight b) * (weight z + weight w))

theorem lagrange_at (a b z w : Amp n) : Γ ⊢[PRAAx] lagrange a b z w := by
  unfold lagrange weight plus minus times Amp.star
  ipra_ring

def lagrangeSentence : Fm PTm 0 := univ 16
  (lagrange (vars 0 1 2 3) (vars 4 5 6 7) (vars 8 9 10 11) (vars 12 13 14 15))
theorem lagrange_closed : [] ⊢[PRAAx] lagrangeSentence := closeUniv 16 (lagrange_at _ _ _ _)

end LeanProofs.IPRA.Analysis.Quantum.Identities
