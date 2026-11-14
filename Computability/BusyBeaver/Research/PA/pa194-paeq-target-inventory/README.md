# PAeq target axiom inventory and a fixed-axiom proof

The module adapts the pinned PA196 inventory to the current Foundation
language: twelve fixed equality/arithmetic formulas and the arbitrary-parameter
induction scheme define `ordinaryPAeq`. `targetFixedTheory` contains exactly
the universally closed fixed formulas and is Δ₁. Its inclusion in
`ordinaryPAeq` is proved.

For every IΣ₁ arithmetic model, `zeroNotSucc_witness` gives the explicit
one-node internal LK proof of the universally closed zero-not-successor axiom
in the finite target theory. `target_axiom_witness` gives the same construction
for any Δ₁ target theory and its standard sentence member. This does not yet
identify any translated source PA axiom with that target sentence, establish a
Δ₁ classifier for the full target induction scheme, or connect the target
theory with the PA194 numerical calculus.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-target-inventory/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
