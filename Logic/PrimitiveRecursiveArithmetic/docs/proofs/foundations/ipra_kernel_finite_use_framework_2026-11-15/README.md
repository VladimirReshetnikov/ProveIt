# Kernel-Facing Finite-Use Framework for iPRA

Prepared from the current `VladimirReshetnikov/ProveIt` iPRA tree on
2026-11-15.

Start with:

- `paper/ipra_kernel_finite_use_framework.pdf` - the complete human-readable
  report and proofs;
- `THEOREM_LEDGER.md` - claim-by-claim status;
- `lean/KernelCompiler.lean` - the generic object-language compiler;
- `FORMALIZATION_ROADMAP.md` - a dependency-ordered path to complete Lean
  integration;
- `verification/verification_report.txt` - actual test/build/audit results.

## Main advance

The repository already has strong finite-observation, certificate, categorical,
and contract-DAG designs.  Their recurrent final gap is the passage from
finite semantic data to a derivation of the actual deep-embedded type

```lean
Gamma |- [PRAAx] phi
```

The recent contract-compiler blueprint still leaves its generic DAG theorem as
`True`, while several neighboring packets provide isolated `Prf PRAAx`
combinators.  This package closes the *generic logical composition* layer.

`ProofBuild Gamma done` is a reverse-topological proof schedule.  Every node
stores a local object derivation from earlier nodes and permanent hypotheses.
`ProofBuild.step` compiles that node by simultaneous cut; the result is again a
collection of genuine embedded derivations.  Repetition compiles any fixed
finite acyclic contract graph.  No host theorem is silently reinterpreted as an
iPRA theorem.

The framework also supplies:

- a QF-induction loop compiler with arbitrary quantified extraction;
- bounded finite relational selection by backward viability and least choice;
- witness-free stable-observable erasure;
- exact branch collapse only under an explicit gap;
- boundary obligations for genuinely global or ineffective mathematics;
- fixed-program specialization, avoiding any universal total evaluator;
- an exact rational cubic-bisection certificate as a worked finite trace.

## What is resolved, and what is not

Resolved at the reusable layer:

1. object-language contract composition;
2. finite loop reflection through quantifier-free induction;
3. bounded finite choice and relational path construction;
4. tie-breaking independence for stable observables;
5. the logical separation between computation, verification, gap data, and
   global boundary theorems.

Not claimed:

- generic effective forms of Siegel, Faltings, Mordell-Weil, Chebotarev, or
  other deep global theorems whose required bounds are not presently supplied;
- exact equality or branch decisions from approximation data without a proved
  separation margin;
- a universal primitive-recursive interpreter;
- completed object-iPRA arithmetic instances for every theorem packet.

The report explains how these remaining issues become explicit fields rather
than hidden assumptions.

## Verification status

- Python reference implementation: standard library only; unit tests pass.
- Certificate examples: independently checked.
- LaTeX: compiled with `latexmk`; PDF text and page rendering inspected.
- Lean: the generic source contains no `sorry`, `admit`, or new axiom, but Lean
  is not installed in this artifact-building runtime.  Therefore the source is
  **not claimed to have been typechecked here**.  It targets Lean 4.32.0 and the
  current ConciseIPRA API.  See `lean/README.md`.

The Python code is regression evidence for finite algorithms, not an iPRA proof
checker.

## Reproduce

```sh
bash build.sh
```

The script runs Python tests, regenerates the Lean schedule and cubic
certificate, compiles the paper, performs static Lean auditing, inspects the
PDF, and refreshes the manifest.

## Suggested repository location

```text
Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/
  ipra_kernel_finite_use_framework_2026-11-15/
```

No remote repository mutation was performed.
