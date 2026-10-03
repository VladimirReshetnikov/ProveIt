# Research and verification status

## Established within this report

The article supplies ordinary mathematical proofs of its explicit resource-envelope,
commutation, quartic accelerator, fixed-block, fixed-word-power, and canonical-history
claims. In particular, the witness-uniqueness proofs include inactive slacks, Boolean
support detection, padding, intermediate states, and auxiliary product gates.

The Python reference implementation passed the recorded finite exact-integer tests.
The separately written JSON checker validated both exported certificates and compared
the expanded polynomials with their residual-square evaluation on 50 seeded assignments
per file. Those comparisons are finite checks, not symbolic identity proofs.

## Known background, not claimed as new

MRDP, machine arithmetization, low-degree functional circuit lifting, and Cartier--Foata
normal forms are existing mathematics. The paper credits the relevant primary sources.
The fixed-word macro result is an elementary closure consequence, included rather than
left as an artificial open problem. Rank and progress corollaries are direct applications
of the explicitly proved compiler contract.

## What is proposed as this report's contribution

The exact combined resource-envelope derivation, the explicit ordinary-polynomial
compiler assemblies with full fibre control, their quantitative counts, and the integration
of causal normal forms with exact guarded resource semantics form the report's substantive
construction. They were developed and proved here. A comprehensive priority search was
not completed, so they are not advertised as established world-first breakthroughs.

## Not established

- No general single-fold or finite-fold MRDP theorem.
- No single fixed-arity canonical polynomial for arbitrary unbounded universal execution.
- No improvement of ProveIt's universal 75-operation certificate.
- No claim that eleven witnesses in the example is optimal.
- No full SKI/Iota evaluation compiler: the article gives a local head-rule component
  with explicit validity and semantics qualifications.
- No Lean or Coq checking of the new results.
- No repository build or rerun of the repository's existing axiom audits.
- No efficient algorithm for solving arbitrary Diophantine equations.

## Domains and semantics that must be preserved

All witness sets are over N = {0,1,2,...}. Subtraction in residuals is evaluated over Z.
Changing to unrestricted integer witnesses invalidates uniqueness claims without an
additional domain encoding. “Independence” means equality of partial sequential maps,
including their domains; it is not simultaneous Petri-token reservation. The height bound
is a compiler parameter controlling arity, not an input to one fixed universal polynomial.
Counts are parameters unless explicitly promoted to existential witnesses.
