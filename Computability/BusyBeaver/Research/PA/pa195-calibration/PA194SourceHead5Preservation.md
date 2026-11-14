# Numerical source head5 preservation

`PA194SourceHead5Preservation.head5` proves that every numerical head5
instance translates to an internally PA-provable formula. Writing
`I(a,b) = 4·cantor(a,b)`, `U(x,p) = 4·cantor(p,x)+2`, and
`E(a,b) = 4·cantor(a,b)+3`, the source code is
`I(U(label, I(E(h,label),1)),1)`. The theorem covers arbitrary model-valued
`label` and `h`, including nonstandard values. Both implication codes are
nonzero, so neither takes the special code-zero alias branch.

The model assumptions are a nonempty model of the candidate PRA language,
with its equality structure, satisfying the candidate PRA axioms, whose
arithmetic reduct satisfies IΣ₁. The conclusion is Foundation's internal PA
provability predicate in that model. This is not a theorem that iPRA proves
PA194's nonhalting equivalence, nor is it a finite proof transformer.

The code `1` does not translate literally to falsity. It translates to the
fixed diagonal bit formula at free label `0`. On specializing the universal
formula at `h`, that label becomes `if label = 0 then h else 0`.
`PA194InternalBitDiagonal.internal_PA_proves_bit_diag_neg` obtains an internal
PA refutation for every model-valued diagonal label by quoting a fixed standard
PA proof and specializing it. The specialized equality is `h = h`; PA proves
that by reflexivity. Together these facts establish the head5 implication.

`PA194ReplacementOpening.specialization_agreement` is the all-model syntax
lemma used for that calculation: a Σ₁-definable replacement of one free label
agrees with Foundation's close-then-open operation on every internally
well-formed formula, including nonstandard ones. It does not assert that a
fixed candidate-PRA code computes that replacement, and it does not assert
semantic truth or preservation of arbitrary derivations.

Run `check-source-head5-preservation.sh` with `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set to the matching audited object overlays. The
script builds the prerequisite modules and all three new modules in a fresh
temporary directory, and rejects `sorryAx` in the printed dependencies.

An independent ordered suffix replay rebuilt the three new modules against
retained source-prerequisite overlays and passed with no `sorryAx`. That
suffix replay did not rebuild all of their prerequisites.
