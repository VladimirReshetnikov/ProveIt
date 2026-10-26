# Independent review of the current arithmetic existence equivalences

Result: PASS. `circuit_reduction` authored `CurrentCarrierArithmetic2011.lean`
and its focused checks; ROOT assigned, reviewed, and freshly replayed them.
`controller_certificate` independently read all134+53
lines and the invoked theorem statements, checked the composition, and
freshly compiled both modules. No reviewed source was edited.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCarrierArithmetic2011.lean | 5f749fdfe0a3857c6d84b0505574f1b1d09f5b859167659a34b04ba392f4a5b3 |
| CurrentCarrierArithmetic2011Checks.lean | b3719b751b6fd7b1d4e405e7588b44140c27dac2e1206dfb19a4cff8507d96d3 |

The complete concrete masks and their equality with the maintained
printed recipes were independently reviewed and reconstructed in
`current-masks2011-lean-peer.md`. In particular, the four-port order here
is exactly `[beta,K,MC,MF_native+beta]`; the high-mask shift is present
once. K is a single integer parameter and all three other ports are the
complete fixed length2011 integers.

`portBounds` derives every `Carrier65Witness.PortBounds` field from the
finite mask results and `K>0`. The beta lower bound is proved by monotonicity
of powers, both masks are positive and strictly below beta, and the
fourth source port lies strictly between beta and twice beta. No rank,
Pell-index, tableau, or machine premise is introduced.

`completes` invokes the proved private-seed construction
`ThirteenCarrierComplete.polynomial_zero_completes`, discharging both its
complete finite `Interface` and its additional `MC mod4=2` hypothesis.
It starts from an actual strictly positive zero of the literal
`Carrier65.polynomial`, produces one strictly positive13-coordinate
assignment, preserves the nine stated outer coordinates, and proves
that this assignment zeros all three literal thirteen-variable forms.
It does not assume existence of the private Pell seed it needs.

`restores` uses the independently formalized explicit restoration map
from a zero of any one of the three thirteen-variable polynomials to a
strictly positive zero of the fourteen-variable polynomial. This direction
requires only the already proved positive beta. The adjacent69/70/71
equivalences preserve the same assignment and correctly use the pair of
equivalences with71; they need no positivity assumption on K. The final
`positive_zero_65_iff_71` is the transitive composition of these actual
positive-zero existence statements, with K>0 required for completeness.

The focused checks unfold the endpoints to the actual multivariate
polynomials, reject the omitted fourth-port shift and the K=0 port-box
claim, and exercise the adjacent thirteen-variable equivalences at K=0.
Their positive domain is explicit: every independent integer coordinate
must be strictly greater than zero.

I independently ran both source files with
`lake env lean -M6000 -j1 -o ...`, writing only to
`/tmp/current-masks2011-peer/`. Both exited0; the main module log is
empty. This is a fresh replay of the two new modules against the checked
dependency environment, not a claimed full fresh dependency rebuild.
The final source hashes remained those above.

| Independent log | SHA-256 |
|---|---|
| arithmetic.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| arithmetic-checks.log | 130db952d45e547e987612addabfc958fe8a174e8e2798b83a06c44f2abc5240 |

All six axiom reports, including both witness maps and the final
existence equivalence, contain only `propext`, `Classical.choice`, and
`Quot.sound`. No missing mathematical assumption was found in this
composition.

The formal result is an arithmetic equivalence for the complete fixed
masks and arbitrary positive K. It does not identify K with the displayed
tableau kernel, provide the remaining native/machine calibration, or
prove an equivalence with Con(ZFC). Those obligations remain separate
from this completed arithmetic composition.
