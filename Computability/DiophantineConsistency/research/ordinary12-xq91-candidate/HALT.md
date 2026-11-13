# Fixed-port all-model halt equivalence

`XQ91Halt.lean` proves that in every model `V` of `IΣ₁`, the 91-operation
graph with the compact symbolic four-port tuple has a strictly positive zero
exactly when

```
∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0.
```

The coordinates and `T` can be nonstandard model elements. Separate theorems
give the same equivalence after substituting `x+1` for each coordinate, and
with the exact closed Lean byte recipes for all four ports. The 91-operation
count applies to the original positive-coordinate evaluator and excludes the
separate coordinate shifts.

The proof establishes a positive-witness equivalence with the accepted
92-graph model theorem. The forward map replaces `X` by `q*w`; the reverse
uses the checked `FreeJGraphCongruenceExplore.symbolic_aligned` theorem to
obtain `X=q*w`, and positivity of `X` yields `w>0`. That theorem internally
derives the necessary beta and low/high-port bounds from the fixed symbolic
tuple and `CompactFixedBeta.beta_identity`, without expanding the large beta
numeral. This converse is a **fixed-port** result, not a claim for arbitrary
integer or natural-number ports.

The bounded author run `observations/halt-attempt04/` exited 0 in 7.6 seconds
with no warnings or `sorryAx`. All five named reports contain only the Lean
metatheory axioms `[propext, Classical.choice, Quot.sound]`. The source and
runner SHA-256 hashes are
`076d89c30680bc31774f2957fc06d1217dc1ac298d3815d3ca8a632e306fc5df` and
`bbdf6281fe2649e43d0b79e368d22ca41d5cbad7a9444b7389aec5d6ae9edb74`;
the exact source and runner are retained with the receipt. Two resource
samples saw at most one Lean process and at least 18,455,396 KiB MemAvailable;
between-sample overlaps or memory dips are not ruled out.

The runner pins the previously checked 1,291-file 92-halt union, adds its
halt object and the two 91 comparison objects, and validates a 1,294-file
selected union before and after compilation. It also pins the independent
serialized-import scan for the planned three-import project closure of 741
modules, checks its recorded inputs and ancestor hashes, and verifies the
selected `FreeJGraphCongruenceExplore` object used by the proof. The final
union retains the 92 model's selected tail object and excludes the known
conflicting top-level binding modules. The checks cover selected project
objects within the audit's scope; complete historical source-to-object,
package-transitive and dynamic ancestry remain inherited. This is one author
build, not an independent Lean replay.

The first attempt hit a kernel memory limit after a high-port cast error and
large-exponent warning. The second had an uncaught monitor-parser error; its
child exit was not observed, so no result is attributed to it. The third
again hit the kernel limit without the earlier warning. Their saved sources,
logs and observations, including the exact limitation of the second attempt,
are retained alongside the successful fourth run. The successful proof uses
the existing symbolic specialization instead of expanding the fixed beta.

This theorem is model-level, not an internal iPRA derivation. The graph/Lean
source, external coefficient payloads and PDF remain connected by external
checks, not a Lean filesystem or PDF semantics theorem. The selected-provider
checks do not prove global equation optimality or ZFC consistency.

With the recorded providers available, choose a fresh attempt name:

```sh
ATTEMPT=attempt05 python3 run-halt.py
```
