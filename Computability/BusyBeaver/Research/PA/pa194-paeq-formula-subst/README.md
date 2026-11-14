# IΣ₁ arithmetic-to-PAeq formula substitution agreement

`formulaCode_subst` proves in every IΣ₁ arithmetic model that the exact
current-Foundation arithmetic-to-PAeq formula translation commutes with
simultaneous substitution:

```
formulaCode param (subst ℒₒᵣ w p) =
  subst PA194PAeq.language (termVector k w) (formulaCode param p).
```

Here `p` is an internally valid arithmetic formula at bound depth `k`, and
`w` is an internally valid term vector of length `k` at any target depth. All
parameters and codes may be nonstandard model elements. The stronger
`formulaCode_subst_internal` needs only unrestricted term-vector validity and
its length.

The proof uses the current Foundation substitution recursor's internal Σ₁
`semiformula_result_induction`, not full-PA induction. Its universal and
existential induction hypotheses apply at the actual changed `qVec` parameter;
the checked term/vector qVec compatibility connects the source and PAeq
branches. Equality and strict-order atom compatibility are proved in the two
prerequisite modules. The upstream PA196 theorem used full-PA induction for
this agreement; this proof is a current-Foundation IΣ₁ adaptation.

This equality does not supply a witness bound or finite PRA code for the
formula-translation graph, an internal PA proof-code compiler, or either
machine/consistency implication. Upstream hashes identify the adapted atomic
proofs; the IΣ₁ formula induction is new in this package.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-formula-subst/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local syntax and compatibility chain and
checking the upstream pins. The exported theorems' axiom audits contained no
`sorryAx`.
