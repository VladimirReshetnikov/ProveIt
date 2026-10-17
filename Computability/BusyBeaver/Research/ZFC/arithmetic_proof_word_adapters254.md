# Quotation and nonemptiness of compiled proof words

The [raw-word history](arithmetic_proof_word254.md) has two checked adapters
with different scopes. Neither changes the proof validator or machine.

[`ArithmeticProofWordQuote254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWordQuote254.lean)
proves, for every ordinary finite `RawProof` tree `p`,

```text
rawWord(p.quote) = CommandWord254.encode(Code254ProofCompiler.compile(p)).
```

This includes invalid trees. The positive proof marker is removed once;
tag and payload recovery then use remainder and quotient by twelve.
Structural induction uses the checked symbolic command blocks, including
both MP premises, GEN's whole-tail premise, and all original leaf fields.
This is exact agreement with the structural compiler on quoted trees. It
does not give an external finite-tree interpretation to every internal code.

[`ArithmeticProofWordNonempty254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWordNonempty254.lean)
proves, for every internal code in every IΣ1 model,

```text
rawWord(code) = 0       ↔ code = 0
compiledWord(code) = 0  ↔ ArithmeticHistory254.value(code) = 0.
```

No acceptance or standardness hypothesis is needed. Every shifted cons is
nonzero; append is zero exactly when both words are zero. Each compiler
block therefore stays nonempty for arbitrary child words. The model's
initial segment below twelve consists of the twelve numerals, so this
argument applies to every internal remainder and hence every positive proof
code. The original validator rejects proof code zero, giving the public
equivalence. Invalid proof zero, empty shifted word zero, and raw command
zero (`MP 0`) remain distinct conventions.

The [quotation verification](results/arithmetic-proof-word-quote254-verification.json)
freshly checks the existing structural compiler, the new adapter and its
two-probe/eighteen-caller audit. The
[nonemptiness verification](results/arithmetic-proof-word-nonempty254-verification.json)
freshly checks its module and twelve-probe/eighteen-caller audit. Both use
only standard Lean axioms and emit no warnings. Each runner reuses 27
explicitly matched project prerequisites from successful raw-word evidence;
it checks actual source, object, compiler and external-provider identities
before and after use, without rebuilding or fetching dependencies.
The [review](results/arithmetic-proof-word-adapters254-review.json) records
independent scope and identity checks. Maintained files are exact copies of
the final checked sources, audits and runners.

Run each checker with a successful raw-word record and a fresh external
scratch directory:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_word_quote254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --word-evidence /outside/successful-proof-word-check/verification.json \
  --output /outside/new-empty-quote-check

python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_word_nonempty254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --word-evidence /outside/successful-proof-word-check/verification.json \
  --output /outside/new-empty-nonempty-check
```

Accepted-proof execution, scheduler and binary-trace transport, and the
internal proof transformations between C254 and ZFC remain open.
