# Finite validator quantifier interface

`ValidatorQuantifierCore254` derives quantifier and vacuity laws directly for
the checked arithmetic predicate CProv. Every formula and label argument is
an arbitrary internal value in any model of IΣ1. The source uses the actual
twelve numeric rule closures and the polymorphic finite `Kalmar.Der` deduction
theorem; it never applies recursion on ordinary Lean formulas to internal
syntax codes.

The source supplies universal/existential monotonicity, existential elimination
from an explicit vacuity theorem, conjunction introduction/projections, and
vacuity through relative negation, implication and universal quantification.
Atomic membership/equality vacuity is projected from the original bundle;
both inequalities remain required. Truth 0 and relative falsity 1 have their
own vacuity proofs, including chosen label 0. No constructor injectivity or
absence of the zero implication alias is assumed.

The final `all_relational H P Q x y` theorem has the exact resources

```
CProv(H -> (Eq(x,y) -> (P -> Q)))
Vac(x,H), Vac(x,Q), Vac(y,H), Vac(y,All(x,P))
------------------------------------------------
CProv(H -> (All(x,P) -> All(y,Q))).
```

Here implication is numeric `wim`, All is `wal`, Eq is `weq`, and
`Vac(i,p)` means CProv(p→All(i,p)). Generalization at x, distribution and
rho1 produce an existential witness for Q; its supplied x-vacuity and rho6
eliminate that existential. Generalization at y uses the other two explicit
vacuity witnesses. The theorem has no hidden x≠y condition or closed-matrix
premise. An eventual paired-environment alpha induction must actually derive
all four vacuity resources; this theorem does not discharge that induction.

The source and audit passed on their first attempt in 3.431626 and 2.353855
seconds: all 25 named axiom probes and 18 callers succeeded, with only
`propext`, `Classical.choice`, `Quot.sound`, and zero warnings. The audit
includes arbitrary internal values, coincident binder labels, zero truth and
falsity, and both gated atomic projections. No proof build followed the PASS.

The narrow runner reuses the exact checked CProv object and its 19 project
ancestors: 20 selected project source/object pairs. Its four cached external
boundaries include three direct boundaries and the inherited explicit Seq
iteration anchor. Actual Init and Omega providers are checked against the
compiler sysroot. All 60 proof inputs and fresh object hashes are checked;
the fresh object is recorded immediately after the source passes and before
the audit. Each compiler command has a 120-second timeout, 4 GiB limit and
one thread, with default options and no dependency builds/downloads.

The earlier unbuilt guard had stale final result counts and lacked a timeout;
it was corrected before the single proof run. Both unbuilt preparations and
the old guard/diff are retained as history. The portable guard changes only
source/audit defaults. Prepare-only queries the compiler version and performs
no source or audit proof build.

```sh
python Logic/Interpretability/ZFCinPA/check_validator_quantifier_core254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh/quantifier-check
```

This finite interface does not represent a formula renamer, establish closure
of arbitrary accepted proofs under renaming, perform environment/alpha
induction, translate Foundation proof codes, reconstruct encoded ZF axioms,
or prove a reverse consistency/binary endpoint. The bundle's dual use of c
as matrix code and variable label remains a reason to avoid rowwise proof
renaming. The next proposed alpha proof compares paired bound stacks under
explicit equality assumptions and uses full PA induction if its formula
complexity exceeds IΣ1.
