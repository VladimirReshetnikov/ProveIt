# Every membership fourth input is too weak, even in combination

Keep truth, MP, theorem-only GEN, rho1–rho6, merged G and the full gated
native C222 bundle. Replace unrestricted rho8 by **any collection of its
instances with a membership code as fourth argument**. The resulting
numerical calculus is PA-provably consistent, by an ordinary finite-model
and derivation-induction proof. This includes the union of all six fixed
orientations, arbitrary label builders, and even all membership-fourth
instances at once. Assuming ZFC consistent, it therefore cannot have its
consistency provably equivalent to Con(ZFC) in ZFC.

The five-value model is supplied by Source 147's separate membership
obstruction supplement. Its stated R(A,B) result extends immediately because
**every membership code has the same value**, irrespective of its labels.
The [independent written proof](proof.md) gives that extension and the exact
native-zero and proof-induction arguments. This strengthens the earlier
[six separate syntactic obstructions](../six-orientations/README.md).
It is not a new Lean/PA kernel theorem or a machine-state result.

The [mixed-union extension](mixed-union/README.md) proves that this same
matrix also validates all `U=A`, `U=C`, `U=truth` and `U=F` families
simultaneously with every membership-fourth instance. `U=B` is outside
that theorem; the separate bounded diagnostics do not settle its calibration.

The carrier is `{0,1,2,3,4}`, designated values are `{3,4}`, truth is 4,
every membership atom (including falsity) is 2, and every equality atom is 3.
The literal implication and uniform quantifier tables are in the unchanged
[model](model.json). All restricted rho8 instances evaluate to 4. The full
bundle evaluates to 3 even without imposing its gate. MP and GEN preserve
designation; course-of-values recursion defines the valuation on every natural
code. `I(0,0)=0` is consistent with the table because `J(4,4)=4`.

The model also validates all identities and equality code 3. It **fails K and
explosion** at reachable natural codes 212 and 52, respectively; adding either
is outside this obstruction. It also fails unrestricted rho8. There is no
claim about arbitrary nonmembership fourth inputs or the separately calibrated
K/S plus quantified-stability calculus. This algebra is a model of numerical
derivability, not an ordinary set-theoretic interpretation of the bundle.

Our [independent finite checker](check.py) directly transcribes the retained
rows and the literal repeated-binder bundle. It imports no submitted code or
parser. Its [first run](result.json) checks 925 schema assignments, 25 MP cases,
five GEN cases, the zero alias, 213 small native-code diagnostics, and explicit
negative controls for unrestricted rho8, K and explosion. The diagnostics do
not replace the all-natural induction. A [separate publication review](peer-review.json)
checked the evaluator against the literal native definitions and written proof. Reproduce using a new output path:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/finite-matrix/check.py --output /tmp/membership-matrix-new.json
```

Provenance: the delivered model and [original source mapping](PROVENANCE.json)
come from `Membership_Fourth_Parameter_Obstruction_2026-10-20.zip`, bundled in
`K218_Contextual_Alternative_2026-10-20.zip` at commit `3c7c3aa5a3`.
[Intake 190](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-190.md)
preserves the complete original supplement, articles and snapshots. Its
original contribution is the five-value/two-designated model and numerical
consistency proof. The intake extends the stated single-orientation result
to arbitrary membership fourth inputs, with independent review by
`review_upstream_reflection` and a separate finite check by `root`.
No supplied wrapper, checksum manifest or Coq/Rocq/Lean executable was run.
