import IPRADerivations.Foundations.GuardedLoop
import IPRADerivations.Foundations.StrategyRealization

/-!
# A typed acyclic FIBER proof compiler

This is an acyclic kernel for `fiber_ipra_2026-11-16`, `thm:compilation` and
`thm:composition`. It compiles actual syntax, recursively combines local
sequents, tracks residual producers, and generates PR symbols for local
metadata. It does not yet implement global runtime demand flattening or the
unrolling of cyclic source graphs, so it is a component of those theorems.

The source indices track the free-variable arity, input context and output
formula. An existential body has one extra variable and its exported goal
must be the shift of the outer goal. A residual `R(c)` within a witness scope
`φ(c)` is exported as the exact obligation `∀ c, φ(c) → R(c)`. This obligation
is stronger than existence of one suitable witness; its strength is explicit.
The compiler never discards a dependency on the local witness.

Residuals under a Boolean branch are guarded by that branch's bit equation.
Residuals in a `bind` body are guarded by the newly established input formula.
Only the selected branch's or reached body's producers must therefore hold.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiberCompiler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedFormulas
open LeanProofs.IPRA.Foundations.TraceReflection (Run A2)
open LeanProofs.IPRA.ClockedDescent (Pat)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ}

/-- A finite local input list, represented as a conjunction ending in truth. -/
def allOf : List (Fm PTm n) → Fm PTm n
  | [] => zero ≐ zero
  | A :: rest => A ⋏ allOf rest

theorem allOf_elim {Δ : List (Fm PTm n)} {Γ : List (Fm PTm n)}
    (h : Δ ⊢[PRAAx] allOf Γ) {A : Fm PTm n} (ha : A ∈ Γ) : Δ ⊢[PRAAx] A := by
  induction Γ with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons B rest ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Prf.andE₁ h
    · exact ih (Prf.andE₂ h) ha

/-- Local runtime terms. Every term is turned into its actual PR symbol. -/
structure Terms (n : ℕ) where
  demand : List (PTm n) := []
  bound : List (PTm n) := []
  verification : List (PTm n) := []
  transformation : List (PTm n) := []
  observation : List (PTm n) := []

def Terms.subst {k : ℕ} (σ : Fin n → PTm k) (ts : Terms n) : Terms k where
  demand := ts.demand.map (Syn.subst σ)
  bound := ts.bound.map (Syn.subst σ)
  verification := ts.verification.map (Syn.subst σ)
  transformation := ts.transformation.map (Syn.subst σ)
  observation := ts.observation.map (Syn.subst σ)

/-- A local operation is supplied as a checked sequent, with its declared terms. -/
structure Primitive (k : ℕ) where
  inputs : List (Fm PTm k)
  output : Fm PTm k
  terms : Terms k
  localProof : inputs ⊢[PRAAx] output

/-- An interface produced earlier, with its named residuals kept separate. -/
structure Interface (k : ℕ) where
  residuals : List (Fm PTm k)
  inputs : List (Fm PTm k)
  output : Fm PTm k
  terms : Terms k
  proof : residuals ++ inputs ⊢[PRAAx] output

/-- A local checked observation-transfer theorem. Witness sealing is a separate
typed constructor; this contract itself introduces no new local variables. -/
structure Observation (k : ℕ) where
  related : Fm PTm k
  property : Fm PTm k
  output : Fm PTm k
  value : PTm k
  localProof : [related, property] ⊢[PRAAx] output

/-- A fixed acyclic schedule, including lexical certificate scopes. A `bind`
shares an earlier result with the remaining schedule. All primitive inputs
must themselves be constructed by recursive source programs. -/
inductive Program : {n : ℕ} → List (Fm PTm n) → Fm PTm n → Type
  | input {n : ℕ} {Γ : List (Fm PTm n)} {A : Fm PTm n} (available : A ∈ Γ) : Program Γ A
  | truth {n : ℕ} {Γ : List (Fm PTm n)} : Program Γ (zero ≐ zero)
  | residual {n : ℕ} {Γ : List (Fm PTm n)} (A : Fm PTm n) : Program Γ A
  | conjunction {n : ℕ} {Γ : List (Fm PTm n)} {A B : Fm PTm n}
      (left : Program Γ A) (right : Program Γ B) : Program Γ (A ⋏ B)
  | bind {n : ℕ} {Γ : List (Fm PTm n)} {A B : Fm PTm n}
      (value : Program Γ A) (body : Program (A :: Γ) B) : Program Γ B
  | primitive {n k : ℕ} {Γ : List (Fm PTm n)} (op : Primitive k) (σ : Fin k → PTm n)
      (inputs : Program Γ (allOf (op.inputs.map (fun A => A.subst σ)))) :
      Program Γ (op.output.subst σ)
  | pair {n : ℕ} {Γ : List (Fm PTm n)} (a b : PTm n) :
      Program Γ (fstT (pairT a b) ≐ a ⋏ sndT (pairT a b) ≐ b)
  | project {n : ℕ} {Γ : List (Fm PTm n)} (code a b : PTm n)
      (shape : Program Γ (code ≐ pairT a b)) :
      Program Γ (fstT code ≐ a ⋏ sndT code ≐ b)
  | fold {n : ℕ} {Γ : List (Fm PTm n)}
      {init : PTm 1} {step : PTm 3} {N : PTm 1} {Inv : Fm PTm 3}
      {G : Fm PTm 1} {A : Fm PTm 2}
      (loop : GuardedLoop.Loop init step N Inv G A) (u : PTm n)
      (guard : Program Γ (Pat G u)) :
      Program Γ (A2 A (Run init step (Syn.subst ![u] N) u) u)
  | search {n : ℕ} {Γ : List (Fm PTm n)} (b : PTm 1) (A : BF) (y : PTm n)
      (existence : Program Γ (fmAt (.ex b A) n y)) :
      Program Γ (lt (bfWit b A y) (at1 b y) ⋏ fmAt A n (pairT (bfWit b A y) y))
  | booleanCase {n : ℕ} {Γ : List (Fm PTm n)} {B : Fm PTm n} (A : BF) (y : PTm n)
      (zeroBranch : Program ((bitAt A n y ≐ zero) :: Γ) B)
      (oneBranch : Program ((bitAt A n y ≐ one) :: Γ) B) : Program Γ B
  | sealExists {n : ℕ} {Γ : List (Fm PTm n)} {A : Fm PTm n} (φ : Fm PTm (n + 1))
      (existence : Program Γ (.ex φ))
      (body : Program (φ :: Γ.map Fm.shift) A.shift) : Program Γ A
  | strategy {n : ℕ} {Γ : List (Fm PTm n)} (P : StrategyRealization.Pattern) (code x : PTm n)
      (check : Program Γ (StrategyRealization.verifier P code x ≐ one)) :
      Program Γ (fmAt (StrategyRealization.formula P) n x)
  | observe {n k : ℕ} {Γ : List (Fm PTm n)} (op : Observation k) (σ : Fin k → PTm n)
      (related : Program Γ (op.related.subst σ))
      (property : Program Γ (op.property.subst σ)) : Program Γ (op.output.subst σ)
  | call {n k : ℕ} {Γ : List (Fm PTm n)} (callee : Interface k) (σ : Fin k → PTm n)
      (inputs : Program Γ (allOf (callee.inputs.map (fun A => A.subst σ)))) :
      Program Γ (callee.output.subst σ)

/-- The producer requirement exported from one lexical witness scope. -/
def sealProducer (φ R : Fm PTm (n + 1)) : Fm PTm n := .all (φ ⟶ R)

/-- Residuals are computed from the source, preserving order and duplicates.
Control-flow assumptions become guards on their local producer formulas. -/
def Program.residuals : {n : ℕ} → {Γ : List (Fm PTm n)} → {A : Fm PTm n} →
    Program Γ A → List (Fm PTm n)
  | _, _, _, .input _ => []
  | _, _, _, .truth => []
  | _, _, _, .residual A => [A]
  | _, _, _, .conjunction p q => p.residuals ++ q.residuals
  | _, _, _, @Program.bind _ _ A _ p q => p.residuals ++ q.residuals.map (fun R => A ⟶ R)
  | _, _, _, .primitive _ _ p => p.residuals
  | _, _, _, .pair _ _ => []
  | _, _, _, .project _ _ _ p => p.residuals
  | _, _, _, .fold _ _ p => p.residuals
  | _, _, _, .search _ _ _ p => p.residuals
  | n, _, _, .booleanCase A y p q =>
      p.residuals.map (fun R => (bitAt A n y ≐ zero) ⟶ R) ++
        q.residuals.map (fun R => (bitAt A n y ≐ one) ⟶ R)
  | _, _, _, .sealExists φ p q => p.residuals ++ q.residuals.map (sealProducer φ)
  | _, _, _, .strategy _ _ _ p => p.residuals
  | _, _, _, .observe _ _ p q => p.residuals ++ q.residuals
  | _, _, _, .call callee σ p => callee.residuals.map (fun A => A.subst σ) ++ p.residuals

/-- Compile into any context deriving the computed residuals and the named
inputs. The recursion inspects source nodes, not an assumed final proof. -/
theorem Program.emit {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A)
    {Δ : List (Fm PTm n)}
    (producers : ∀ R ∈ p.residuals, Δ ⊢[PRAAx] R)
    (inputs : ∀ B ∈ Γ, Δ ⊢[PRAAx] B) : Δ ⊢[PRAAx] A := by
  induction p with
  | input available => exact inputs _ available
  | truth => exact .eqRefl _
  | residual A => exact producers A List.mem_cons_self
  | conjunction p q ihp ihq =>
    exact .andI (ihp (fun R hR => producers R (List.mem_append_left _ hR)) inputs)
      (ihq (fun R hR => producers R (List.mem_append_right _ hR)) inputs)
  | bind p q ihp ihq =>
    have value := ihp (fun R hR => producers R (List.mem_append_left _ hR)) inputs
    apply ihq (fun R hR => .impE
      (producers _ (List.mem_append_right _ (List.mem_map.2 ⟨R, hR, rfl⟩))) value)
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact value
    · exact inputs B hB
  | primitive op σ p ih =>
    have args := ih producers inputs
    exact (op.localProof.subst σ).trans (fun _ h => allOf_elim args h)
  | pair a b => exact .andI (fst_pair _ _) (snd_pair _ _)
  | project code a b p ih =>
    have shape := ih producers inputs
    exact .andI ((congrFst shape).eqTrans (fst_pair _ _))
      ((congrSnd shape).eqTrans (snd_pair _ _))
  | fold loop u p ih => exact GuardedLoop.loop_at loop u (ih producers inputs)
  | search b A y p ih => exact bf_choice b A y (ih producers inputs)
  | booleanCase A y p q ihp ihq =>
    refine .orE (bf_cases A y) ?_ ?_
    · apply ihp (fun R hR => .impE
        (producers _ (List.mem_append_left _ (List.mem_map.2 ⟨R, hR, rfl⟩))).wk Prf.hyp0)
      intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact Prf.hyp0
      · exact (inputs B hB).wk
    · apply ihq (fun R hR => .impE
        (producers _ (List.mem_append_right _ (List.mem_map.2 ⟨R, hR, rfl⟩))).wk Prf.hyp0)
      intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact Prf.hyp0
      · exact (inputs B hB).wk
  | sealExists φ p q ihp ihq =>
    have existence := ihp (fun R hR => producers R (List.mem_append_left _ hR)) inputs
    refine .exE existence ?_
    apply ihq
    · intro R hR
      have sealed := producers (sealProducer φ R)
        (List.mem_append_right _ (List.mem_map.2 ⟨R, hR, rfl⟩))
      exact .impE sealed.allOpen.wk Prf.hyp0
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact Prf.hyp0
      · rcases List.mem_map.1 hB with ⟨C, hC, rfl⟩
        exact (inputs C hC).shift.wk
  | strategy P code x p ih => exact StrategyRealization.strategy_sound P code x (ih producers inputs)
  | observe op σ p q ihp ihq =>
    have related := ihp (fun R hR => producers R (List.mem_append_left _ hR)) inputs
    have property := ihq (fun R hR => producers R (List.mem_append_right _ hR)) inputs
    apply (op.localProof.subst σ).trans
    intro B hB
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · exact related
    · exact property
  | call callee σ p ih =>
    have args := ih (fun R hR => producers R (List.mem_append_right _ hR)) inputs
    apply (callee.proof.subst σ).trans
    intro B hB
    rw [List.map_append] at hB
    rcases List.mem_append.1 hB with hR | hI
    · exact producers B (List.mem_append_left _ hR)
    · exact allOf_elim args hI

/-- The literal compiled sequent, with precisely the computed residual list. -/
theorem Program.compile {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A) :
    p.residuals ++ Γ ⊢[PRAAx] A :=
  p.emit (fun _ hR => .hyp (List.mem_append_left _ hR))
    (fun _ hB => .hyp (List.mem_append_right _ hB))

/-- Residual discharge is simultaneous cut into any client context. -/
theorem Program.discharge {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A)
    {Δ : List (Fm PTm n)} (producers : ∀ R ∈ p.residuals, Δ ⊢[PRAAx] R)
    (inputs : ∀ B ∈ Γ, Δ ⊢[PRAAx] B) : Δ ⊢[PRAAx] A :=
  p.compile.trans (fun B hB => by
    rcases List.mem_append.1 hB with hR | hI
    · exact producers B hR
    · exact inputs B hI)

/-- The compiler constructs a symbol from its body instead of accepting an
unverified function symbol with an asserted relationship to the body. -/
structure GeneratedSymbol (n : ℕ) where
  body : PTm n

def GeneratedSymbol.program (s : GeneratedSymbol n) : PR n := PTm.toPR s.body

/-- Correctness of every generated PR symbol at arbitrary client terms. -/
theorem GeneratedSymbol.correct (s : GeneratedSymbol n) {m : ℕ} (σ : Fin n → PTm m)
    {Γ : List (Fm PTm m)} :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app s.program σ ≐ Syn.subst σ s.body := toPR_eq s.body σ

structure Symbols (n : ℕ) where
  demand : List (GeneratedSymbol n)
  bound : List (GeneratedSymbol n)
  verification : List (GeneratedSymbol n)
  transformation : List (GeneratedSymbol n)
  observation : List (GeneratedSymbol n)

def Terms.symbols (ts : Terms n) : Symbols n where
  demand := ts.demand.map GeneratedSymbol.mk
  bound := ts.bound.map GeneratedSymbol.mk
  verification := ts.verification.map GeneratedSymbol.mk
  transformation := ts.transformation.map GeneratedSymbol.mk
  observation := ts.observation.map GeneratedSymbol.mk

def Terms.append (left right : Terms n) : Terms n where
  demand := left.demand ++ right.demand
  bound := left.bound ++ right.bound
  verification := left.verification ++ right.verification
  transformation := left.transformation ++ right.transformation
  observation := left.observation ++ right.observation

inductive NodeKind where
  | input | truth | residual | conjunction | bind | primitive | pair | project
  | fold | search | booleanCase | strategy | observe | call

/-- Metadata retains lexical scope. Terms depending on a local witness have
arity `n+1` under `localScope`, rather than escaping into the outer block. -/
inductive Metadata : ℕ → Type
  | block {n : ℕ} (kind : NodeKind) (terms : Terms n) : Metadata n
  | unary {n : ℕ} (kind : NodeKind) (terms : Terms n) (child : Metadata n) : Metadata n
  | binary {n : ℕ} (kind : NodeKind) (terms : Terms n) (left right : Metadata n) : Metadata n
  | localScope {n : ℕ} (existence : Metadata n) (body : Metadata (n + 1)) : Metadata n

/-- Only terms with the outer arity are exported. Local body metadata remains
available in the scope tree and is never silently coerced to an outer term. -/
def Metadata.exportedTerms : {n : ℕ} → Metadata n → Terms n
  | _, .block _ terms => terms
  | _, .unary _ terms child => terms.append child.exportedTerms
  | _, .binary _ terms left right => (terms.append left.exportedTerms).append right.exportedTerms
  | _, .localScope existence _ => existence.exportedTerms

/-- Generate metadata from actual source operations. A fold contributes its
actual run and bound; reflected checks contribute actual verifier terms. -/
def Program.metadata : {n : ℕ} → {Γ : List (Fm PTm n)} → {A : Fm PTm n} →
    Program Γ A → Metadata n
  | _, _, _, .input _ => .block .input {}
  | _, _, _, .truth => .block .truth {}
  | _, _, _, .residual _ => .block .residual {}
  | _, _, _, .conjunction p q => .binary .conjunction {} p.metadata q.metadata
  | _, _, _, .bind p q => .binary .bind {} p.metadata q.metadata
  | _, _, _, .primitive op σ p => .unary .primitive (op.terms.subst σ) p.metadata
  | _, _, _, .pair a b => .block .pair
      { verification := [eqb (fstT (pairT a b)) a * eqb (sndT (pairT a b)) b]
        transformation := [pairT a b]
        observation := [fstT (pairT a b), sndT (pairT a b)] }
  | _, _, _, .project code a b p => .unary .project
      { verification := [eqb code (pairT a b)]
        observation := [fstT code, sndT code] } p.metadata
  | _, _, _, @Program.fold _ _ init step N _ _ _ _ u p => .unary .fold
      { demand := [Syn.subst ![u] N]
        bound := [Syn.subst ![u] N]
        transformation := [Run init step (Syn.subst ![u] N) u] } p.metadata
  | n, _, _, .search b A y p => .unary .search
      { demand := [y]
        bound := [at1 b y]
        verification := [bitAt A n (pairT (bfWit b A y) y)]
        transformation := [bfWit b A y] } p.metadata
  | n, _, _, .booleanCase A y p q => .binary .booleanCase
      { demand := [y], verification := [bitAt A n y] } p.metadata q.metadata
  | _, _, _, .sealExists _ p q => .localScope p.metadata q.metadata
  | _, _, _, .strategy P code x p => .unary .strategy
      { demand := [x]
        verification := [StrategyRealization.verifier P code x]
        transformation := [code] } p.metadata
  | _, _, _, .observe op σ p q => .binary .observe
      { observation := [Syn.subst σ op.value] } p.metadata q.metadata
  | _, _, _, .call callee σ p => .unary .call (callee.terms.subst σ) p.metadata

/-- The fixed PR symbols generated for all outer-scope local metadata. The
scope tree separately retains symbols requiring a local certificate argument. -/
def Program.symbols {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A) : Symbols n :=
  p.metadata.exportedTerms.symbols

/-- Package compiler output and generated outer-scope metadata for a later
typed call node. No final theorem or metadata-correctness proof is supplied. -/
def Program.toInterface {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (p : Program Γ A) : Interface n where
  residuals := p.residuals
  inputs := Γ
  output := A
  terms := p.metadata.exportedTerms
  proof := p.compile

/-- A compiled source theorem specializes at arbitrary object terms. -/
theorem Program.compile_at {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A)
    {m : ℕ} (σ : Fin n → PTm m) :
    p.residuals.map (fun R => R.subst σ) ++ Γ.map (fun B => B.subst σ) ⊢[PRAAx] A.subst σ := by
  simpa only [List.map_append] using p.compile.subst σ

/-- Universal closure of the acyclic compiled contract, including every
residual and input in the explicitly printed antecedent. -/
theorem Program.compile_closed {Γ : List (Fm PTm n)} {A : Fm PTm n} (p : Program Γ A) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n (allOf (p.residuals ++ Γ) ⟶ A) := by
  apply closeUniv n
  apply Prf.impI
  exact p.compile.trans (fun _ h => allOf_elim Prf.hyp0 h)

/-- Statically call a compiled source program at one finite specialization. -/
def Program.callCompiled {k : ℕ} {Δ : List (Fm PTm k)} {B : Fm PTm k}
    (callee : Program Δ B) (σ : Fin k → PTm n) {Γ : List (Fm PTm n)}
    (inputs : Program Γ (allOf (Δ.map (fun C => C.subst σ)))) : Program Γ (B.subst σ) :=
  .call callee.toInterface σ inputs

/-- Specialized residuals of the callee are retained before the caller's
input-producer residuals. No duplicate removal or demand normalization occurs. -/
theorem Program.callCompiled_residuals {k : ℕ} {Δ : List (Fm PTm k)} {B : Fm PTm k}
    (callee : Program Δ B) (σ : Fin k → PTm n) {Γ : List (Fm PTm n)}
    (inputs : Program Γ (allOf (Δ.map (fun C => C.subst σ)))) :
    (callee.callCompiled σ inputs).residuals =
      callee.residuals.map (fun R => R.subst σ) ++ inputs.residuals := rfl

/-- A producer in the rest of a schedule is needed only after its bound
intermediate formula has been established. -/
theorem Program.bind_residuals {Γ : List (Fm PTm n)} {A B : Fm PTm n}
    (value : Program Γ A) (body : Program (A :: Γ) B) :
    (Program.bind value body).residuals =
      value.residuals ++ body.residuals.map (fun R => A ⟶ R) := rfl

/-- Boolean branch producers retain the exact reflected bit guard. -/
theorem Program.booleanCase_residuals {Γ : List (Fm PTm n)} {B : Fm PTm n}
    (A : BF) (y : PTm n)
    (zeroBranch : Program ((bitAt A n y ≐ zero) :: Γ) B)
    (oneBranch : Program ((bitAt A n y ≐ one) :: Γ) B) :
    (Program.booleanCase A y zeroBranch oneBranch).residuals =
      zeroBranch.residuals.map (fun R => (bitAt A n y ≐ zero) ⟶ R) ++
        oneBranch.residuals.map (fun R => (bitAt A n y ≐ one) ⟶ R) := rfl

/-- A lexical producer requirement is universally guarded by the exact local
witness formula; no body residual is erased by existential elimination. -/
theorem Program.sealExists_residuals {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (φ : Fm PTm (n + 1)) (existence : Program Γ (.ex φ))
    (body : Program (φ :: Γ.map Fm.shift) A.shift) :
    (Program.sealExists φ existence body).residuals =
      existence.residuals ++ body.residuals.map (fun R => .all (φ ⟶ R)) := rfl

/-- The existential body retains its larger arity in the generated metadata. -/
theorem Program.sealExists_metadata {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (φ : Fm PTm (n + 1)) (existence : Program Γ (.ex φ))
    (body : Program (φ :: Γ.map Fm.shift) A.shift) :
    (Program.sealExists φ existence body).metadata =
      .localScope existence.metadata body.metadata := rfl

/-- A concrete source program performs checked least search using a named
existence producer, with no externally supplied proof of the search result. -/
def boundedSearch (b : PTm 1) (A : BF) (y : PTm n) : Program ([] : List (Fm PTm n))
    (lt (bfWit b A y) (at1 b y) ⋏ fmAt A n (pairT (bfWit b A y) y)) :=
  .search b A y (.residual (fmAt (.ex b A) n y))

theorem boundedSearch_residuals (b : PTm 1) (A : BF) (y : PTm n) :
    (boundedSearch b A y).residuals = [fmAt (.ex b A) n y] := rfl

theorem boundedSearch_compiled (b : PTm 1) (A : BF) (y : PTm n) :
    [fmAt (.ex b A) n y] ⊢[PRAAx]
      lt (bfWit b A y) (at1 b y) ⋏ fmAt A n (pairT (bfWit b A y) y) := by
  simpa only [boundedSearch, Program.residuals, List.append_nil] using (boundedSearch b A y).compile

/-- The concrete search program generates its actual least-search transformer. -/
theorem boundedSearch_transformer (b : PTm 1) (A : BF) (y : PTm n) :
    (boundedSearch b A y).symbols.transformation = [⟨bfWit b A y⟩] := rfl

/-- The generated transformer symbol is proved equal to bounded least search
after every substitution of client terms. -/
theorem boundedSearch_transformer_correct (b : PTm 1) (A : BF) (y : PTm n)
    {m : ℕ} (σ : Fin n → PTm m) {Γ : List (Fm PTm m)} :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app (PTm.toPR (bfWit b A y)) σ ≐
      Syn.subst σ (bfWit b A y) :=
  GeneratedSymbol.correct ⟨bfWit b A y⟩ σ

end LeanProofs.IPRA.Foundations.FiberCompiler
