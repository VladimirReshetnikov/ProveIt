# Reverse membership rewriting in the PA194 calculus

`PA194Logic.reverseAll` constructs, for arbitrary numeric labels `a`, `b`,
and `d`, a finite PA194-calculus derivation of

```text
E(a,b) → (χ(b) → χ(a))
```

for `χ(t) = M(t,d)`, `M(d,t)`, or `M(t,t)`. There are no label-distinctness
assumptions in the final theorem. The proof separately handles `a=b`, the
fixed-parameter collision `d=a`, and the remaining distinct-label cases.
The latter choose the actual code `c = ¬(E(a,b) → (χ(b) → χ(a)))`, prove
its required label bounds, use the old gate's negative separation tail and
the self-diagonal head, and apply the negative-property specialization
lemma. The proof does not assume equality vacuity. The final theorem prints
`[propext, Classical.choice, Quot.sound]`.

The supporting modules adapt the upstream PA196 finite proof templates to the
actual separate-diagonal PA194 derivation type. In particular, the legacy
numeric `bundle` abbreviation is not an added axiom. This proves one of the
report's required equality interfaces in standard Lean. It does not yet
establish the full PA-refutation translation, the reverse soundness
calibration, or an equivalence inside PRA/iPRA. The source tree retains the
pinned Python grammar-translation boundary in `../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-reverse-rewrite/check.sh
```

The script rebuilds the finite source-calculus compiler and bundled-diagonal
prerequisites in private tmpfs, then kernel-checks all reverse-rewrite modules.
The full standalone fresh script has passed, as has an independent replay
of the reverse-rewrite modules from retained clean prerequisites.
