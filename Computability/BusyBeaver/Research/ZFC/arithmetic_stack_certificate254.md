# Bounded actual proof witnesses for theorem stacks

[`ArithmeticStackCertificate254`](../../Lean/BusyBeaver/ZFC/ArithmeticStackCertificate254.lean)
provides the certificate substrate for reverse arithmetic scheduler soundness. Every proof code, formula, stream and stream index may be internal to an arbitrary IΣ₁ model. All witnesses use the actual checked twelve-rule numeric validator.

`ProvB(B,x)` is `∃p≤B, value(p)=x+1`. `StackB(B,z)` requires `1≤B` and certifies the first component of `tailIter(k,z)` for every `k≤z`. These predicates are Δ₁ using the actual total Δ₁ value/tail graphs. The global bound is carried explicitly; no bound for an arbitrary preexisting proof stream is assumed.

The checked [Cantor-tail drain](arithmetic_stack_tail254.md) says that every index at or above numeric stream code `z` reads zero. Truth formula0 has literal proofcode1, which remains available because `1≤B`. Consequently `stack_full` derives certification at every internal offset from the bounded certificate. This unbounded consequence is a local lemma, not the time-induction predicate. Head, push, pop and bound-weakening preserve the exact certificate. `pushList` is only an external finite-list convenience for fixed runtime pushes; no external list enters the arithmetic invariant or the claim about arbitrary internal stream indices.

`WorkingB(B,w)` certifies the top, cache and stream in the actual unshifted working-state code `P(top,P(stack,P(d,cache)))`. The additive register needs no logical witness. `WorkingB` is Δ₁ and `CertifiedWorking(w) := ∃B WorkingB(B,w)` is Σ₁. The allzero working code is certified with bound1. Cached formula1 yields an actual bounded proofcode with validator value2.

The explicit bound extension `extendBound(B,p)=B+p+1` contains both old bound B and a new witness p. This needs no uniform constructor-size bound or choice of every stack witness. Repeating this finite extension can cover the finitely many proofs created by a runtime command.

No runtime command preservation, scheduler time induction, converse PA theorem, binary transport or ZFC proof-code translation is proved here. Arbitrary dirty working states are not silently certified; cache1 may halt immediately without any proof witness.

The [fresh check](results/arithmetic-stack-certificate254-verification.json)
uses twenty project source/object prerequisites from checked Tail14/15 and Constructors17/18 records, plus four identified first external providers. Only this module and its focused 24-probe/17-caller audit are built. All input/source/object/compiler/provider identities and dependency pins are checked before and after, with no dependency build or fetch. The final run2 passes with source5.625s, audit2.278s, zero warnings and only `propext`, `Classical.choice`, `Quot.sound`. The first audit's final finite-list caller needed a membership simplifier correction; no mathematical source change followed the source check. The
[independent review](results/arithmetic-stack-certificate254-review.json)
checks the full source, audit and exact artifacts.

The maintained portable checker is `check_arithmetic_stack_certificate254.py`, with frozen source/audit defaults and exact ordered 24/17 checks. It takes `--repo`, `--dependency-root`, `--tail-evidence`, `--constructor-evidence`, optional separate `--tail-cache` and `--constructor-cache`, and `--output`. `--prepare-only` performs preflight/postchecks without invoking Lean. Explicit source/audit overrides are recorded by their actual hashes. Successful proof evidence and prepare-only evidence remain distinct.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_stack_certificate254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --tail-evidence /outside/successful-stack-tail/verification.json \
  --constructor-evidence /outside/successful-proof-constructors/verification.json \
  --output /outside/new-empty-stack-certificate-check
```
