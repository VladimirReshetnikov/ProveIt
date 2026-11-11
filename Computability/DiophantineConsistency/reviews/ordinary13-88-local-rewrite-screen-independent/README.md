# Independent review: bounded 88/30 local rewrite screens

**PASS, with the scope distinction below.** The two exact-target modular
search receipts and the structural beam receipt replayed byte-for-byte in
this review. Neither search found a live-count improvement within its
recorded enumeration; neither proves a global lower bound, excludes general
same-zero transformations or witness changes, or constitutes a Lean result.

The one- and two-gate exact-target searches each ran on port-uniform samples
and on authenticated fixed-port samples. Their three modular samples are a
one-sided rejection filter: any exact integer identity in an enumerated form
must match all samples, but matching samples alone would not prove an identity.
No target or nonconstant divisor vanished at any recorded sample, so the
recorded division queries do not miss a case due to sampled zero. The direct
alias and square-only sign helper was run **only with port-uniform samples**;
the fixed-port pass did not separately run that helper. This distinction
matters because specializing ports could create aliases absent uniformly.

Independently counting the earlier operands gives n=22,...,109 and
`sum(2n²+n)=874412` first gates. Three additive queries per operand plus one
multiplicative query except the zero literal give `sum(4n−1)=22968` second
queries. Both counts match each receipt. The double-negation control detects
an alias. The structural beam has fixed seed, width 300, ten depths and a
90-gate intermediate cap; its sharing recount and three-to-two factor
control check, but pruning leaves the search nonexhaustive.

The checker pins both search sources and receipts, checks the independently
computed counts and residual scopes, and verifies the basic integer-ring
reassembly/factoring identities. `--replay` reruns both author scripts with
bounded timeouts and compares exact output; the mathematical review already
performed these replays. It does not import or run Lean.
