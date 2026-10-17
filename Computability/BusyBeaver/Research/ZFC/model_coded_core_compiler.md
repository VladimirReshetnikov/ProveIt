# Finite proof templates with internal free parameters

The reusable
[`ModelCodedPredicateHygiene`](../../../../Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPredicateHygiene.lean) and
[`ModelCodedCoreCompiler`](../../../../Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedCoreCompiler.lean)
modules specialize a standard finite proof at an arithmetic matrix whose code
and free-variable labels may be nonstandard. The target is an arbitrary
represented theory in an IΣ1 model. No `FVFree` or `S.shift = S` premise is
required. The result is actual target proof data, accepted by Foundation's
represented `Proof` predicate.

This resolves a restriction of the existing finite-template interface. It does
not yet translate an arbitrary internally coded source proof or prove the
machine's internal PA consistency equivalence.

## Why the proof presentation matters

The previous compiler uses `Derivation2`, which includes an explicit shift
rule. Its translation record keeps the same inserted matrix on both sides of
that rule; the existing predicate client therefore requires `S.shift = S`.
An arbitrary matrix with free parameters need not satisfy this equality.

Foundation's ordinary `Theory.Proof` already stores a standard finite axiom
list and a derivation in the smaller `Basic.Derivation` calculus. That calculus
has identity, cut, contraction, truth, disjunction, conjunction, universal and
existential rules. It has no separate shift constructor. The new compiler
works directly with this derivation.

Two heterogeneous identities supply the binder bookkeeping:

```text
translate(S.shift, shift p) = shift (translate(S, p))
translate(S.shift, free p)  = free (translate(S, p))
```

The universal-rule premise is compiled with `S.shift`; every other recursive
call retains `S`. This preserves both the newly introduced eigenvariable and
all existing internal free parameters. No inverse shift or theory-wide
free-variable renaming is needed.

## Axiom discharge is explicit

For a standard proof `d : T₁ ⊢! σ`, the interface asks for actual proofs of
the translations of the finitely many axioms occurring in `d.axioms`:

```text
hA : ∀ ψ ∈ d.axioms, target ⊢! translate(S, emb ψ)
compileTemplate(S, d, hA) : target ⊢! translate(S, emb σ)
```

These witnesses may be derived proofs. The translated formula need not be a
literal member of the target axiom recognizer. The compiler first translates
the logical derivation, then cuts the supplied witnesses against its negative
axiom context at the root. Thus its binder recursion does not assume that
arbitrary target axioms are preserved under free-variable renaming.

`compileTemplate_isProof` states that the resulting numeric proof value
satisfies the target's represented `Proof` predicate. The source proof and
placeholder arity remain standard finite objects. The matrix is genuinely
internal; it need not be the quotation of a standard formula.

## The lifted-PA client

[`ModelCodedPeanoCore`](../../../../Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPeanoCore.lean)
now supplies the finite axiom witnesses automatically for a proof over lifted
PA. Those source axioms contain no placeholder, so the existing translation
identity maps each one to its ordinary quoted PA axiom, independently of the
inserted matrix. The actual target axiom constructor provides its proof.

`compilePeanoTemplateOpen` therefore accepts any typed internal matrix and a
standard lifted-PA proof, without an extra support or axiom-discharge premise.
`compilePeanoTemplateOpen_isPAProof` exposes the represented PA proof predicate
for its output. The model need only satisfy IΣ1: the result is internal PA
proof data, rather than an assertion that the translated conclusion is true
in that model. Lifted PA does not silently acquire induction axioms containing
the added placeholder.

The [client verification](results/model-coded-peano-core-verification.json)
freshly checks all five local modules and three audits from their maintained
paths: nine axiom reports and twenty callers. The client itself contributes
three reports and six callers, with no warnings. The
[independent client review](results/model-coded-peano-core-review.json)
confirms this scope. The earlier APIs and final-theorem facade remain unchanged.

The subsequent [fixed-template graph](model_coded_template_graph.md) gives
this formula substitution a parameter-free Σ1/Δ1 arithmetic representation.
It also proves an actual IΣ1/PA sentence quantifying over every internal
matrix for each fixed standard source proof. The source-proof standardness
boundary remains explicit.

## Boundary for the set-theoretic comparison

Fixed logical and axiom templates are useful components of the planned
proof-code transformations. A full translation still needs represented syntax
operations, proof selectors and correctness for every internally coded source
proof. None follows just from recursion on this standard source derivation.

The Choice-removal step also has a separate schema issue. Treating an arbitrary
inserted predicate as an uninterpreted symbol does not automatically give
Separation or Replacement in L for that predicate. Their transport must use
the actual source set-language formula code and its relativization. The
existing semantic L results do not by themselves supply this represented
proof selector.

The [PA internalization plan](pa_internalization.md) retains these obligations.
These modules do not alter the 252-state transition table.

## Verification

The [scoped verification](results/model-coded-core-compiler-verification.json)
freshly checks both existing local prerequisites and both new modules, then
six named axiom reports and fourteen callers. Every report lists only Lean's
three standard axioms. The calls include a matrix with free variables 17 and
18, the universal rule, arbitrary target theories and finite axiom discharge.
The check records nine existing prerequisite linter warnings and one new
`unnecessarySimpa` warning. The
[independent review](results/model-coded-core-compiler-review.json) checks the
source, audit and recorded dependencies. Neither the project umbrella nor
the external dependency closure was rebuilt.

The runner uses the pinned, already built Foundation and Mathlib checkout.
It performs no dependency build or download:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_model_coded_core_compiler.py \
  --sources Logic/PeanoArithmetic/BoundedConsistency/Lean \
  --dependency-root /path/to/built/dependency-checkout \
  --lean /path/to/lean-4.32.0/bin/lean \
  --hygiene-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPredicateHygieneAudit.lean \
  --core-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedCoreCompilerAudit.lean \
  --output /outside/new-empty-template-check
```

To include the PA client and its audit, add
`--peano-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPeanoCoreAudit.lean`.
The five-module client replay used this option and the current maintained
runner. The runner explicitly rejects Python's `-O` mode, whose removal of
assertions would invalidate its checks.
