import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Descent

/-!
# Compiling terms to primitive-recursive symbols (`ipra_resources_and_elimination_2026-11-15`, `thm:term-compile`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 3, "The new term-to-symbol
compiler": "Define a compiler `S : PTm k → PR k` by `S(x_i) = proj_i`,
`S(f(t_0, …, t_{m−1})) = comp(f, S(t_0), …, S(t_{m−1}))`", and theorem `thm:term-compile`: "For
every term `t`, arbitrary tuple of substituted terms `σ`, and arbitrary context `Γ`, there is
an embedded arithmetic proof `Γ ⊢ app(S(t), σ) = t[σ]`." Proof: "Induct on the finite syntax of
`t` in the metatheory. For a variable, the projection axiom gives the equation. For an
application, the composition axiom gives ... Equality congruence and transitivity replace those
arguments by `t_i[σ]`."

The packet's own Lean file proves this against a copy of the kernel; here it is in the
derivation library, against the kernel used by every other module:

* `symbol t`: the compiled symbol `S(t)`;
* `symbol_correct`: `Γ ⊢ app (symbol t) σ = t[σ]`, at arbitrary arguments and contexts;
* `transport_equation`: an equation about `t[σ]` is an equation about the compiled symbol;
* `symbol_inst1`, `symbol_inst2`: the unary and binary cases in the notation of the library,
  `ap1 (symbol t) a = inst1 t a` and `ap2 (symbol t) a b = inst2 t a b`.

So a term with parameters can be used wherever a symbol of the corresponding arity is
required (bounded sums, recursions, searches), with the bridging equation derived.
-/

namespace LeanProofs.IPRA.Foundations.TermCompiler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-- A term over `k` parameters becomes one primitive-recursive symbol of arity `k`. -/
def symbol {k : ℕ} : PTm k → PR k
  | .var i => .proj i
  | .app f ts => .comp f (fun i => symbol (ts i))

/-- `thm:term-compile`: the compiled symbol applied to arguments equals the substituted
term. -/
theorem symbol_correct {k n : ℕ} (t : PTm k) (σ : Fin k → PTm n) {Γ : List (Fm PTm n)} :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app (symbol t) σ ≐ Syn.subst σ t := by
  induction t with
  | var i => exact PRA.proj i σ
  | app f ts ih =>
    apply Prf.eqTrans (PRA.comp f (fun i => symbol (ts i)) σ)
    simpa using (Prf.eqCongr (ConciseIPRA.PTm.app f Syn.var) ih)

/-- An equation about a substituted term is an equation about its compiled symbol. -/
theorem transport_equation {k n : ℕ} (t : PTm k) (σ : Fin k → PTm n) {Γ : List (Fm PTm n)}
    {u : PTm n} (h : Γ ⊢[PRAAx] Syn.subst σ t ≐ u) :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app (symbol t) σ ≐ u :=
  Prf.eqTrans (symbol_correct t σ) h

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The unary case: `S(t)(a) = t(a)`. -/
theorem symbol_inst1 (t : PTm 1) (a : PTm n) :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app (symbol t) ![a] ≐ inst1 t a :=
  symbol_correct t ![a]

/-- The binary case: `S(t)(a, b) = t(a, b)`. -/
theorem symbol_inst2 (t : PTm 2) (a b : PTm n) :
    Γ ⊢[PRAAx] ap2 (symbol t) a b ≐ inst2 t a b :=
  symbol_correct t ![a, b]

end LeanProofs.IPRA.Foundations.TermCompiler
