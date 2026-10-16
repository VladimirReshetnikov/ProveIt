# Compiling the one-schema PSC template: a partial experiment

This experiment reaches a **252-state named Wade table**, with 190 decision
states and 62 framework states, using the accepted equality-free subset-PSC
proposal and a genuine falsity code. It retains original rho6. It is a new
partial compiler experiment, distinct from `raw-candidate-252.tm`. Its retained
logical calculus is inadequate: a concrete algebraic interpretation validates
all its emitted axioms while invalidating ordinary quantifier specialization.
It is therefore **not a calibrated ZFC-consistency machine**. No halting theorem
for the binary table is claimed.

The mathematical input is batch144 source08, the one-schema manuscript accepted
in placement `ac4287e5b`, whose ordinary hereditary-saturation interpretation
removes profile congruence from equality-free PSC. This experiment tests the
cost of that schema; it does not implement the reference checker's complete
K/S/C/UI/UD calculus. The equality-free retained logical skeleton is inherited
from the earlier experiment by deleting equality machinery, which needs its
own completeness repair.

## Fresh matrix adapter

The matrix code is c. Its designated free-variable slots are 0 and 1; other
free names remain parameters, and bound occurrences retain their original
scope. Set k=c+2. Use the following curried PSC formula, with `Sub(x,y,z)`
abbreviating `All(z,Rel(z,x)→Rel(z,y))`:

```
SB = All(0, Exists(k, All(1, phi → Sub(1,k,0))))
guard = Sub(0,1,k) OR Rel(0,k)
closed = All(0, guard → All(1, phi → Rel(1,k)))
support = All(1, Rel(1,k) → Exists(0,phi))
PSC = SB → All(1, Exists(k, closed AND support)).
```

The root uses name1 only in the guard before the inner output quantifier
shadows it. The local-bound and hull binders k have disjoint scopes; the
initial subset test may shadow k as its dummy variable. No matrix occurrence
is inserted inside that dummy's scope. These scope distinctions are essential.
The accepted uncurried PSC wrapper is classically equivalent because its guard
does not depend on the freshly bound output. That ordinary currying fact is
not an implemented exact-code proof translation here.

Every variable label of a decoded positive formula lies below its numeric code;
code0 is explicit Truth with no labels. Thus k=c+2 is fresh and distinct from
0/1 for every code, including codes0/1. Copying c into a pushed top and adding
two costs less than an independent c≥2 gate and avoids omitting low-code
matrices. No assumption that matrix variable values are distinct is made.

`psc_adapter_checks.py` independently builds a six-fresh-label **curried**
reference wrapper and compares de Bruijn normal forms for 4894 matrices,
including shadowed 0/1 binders, negative formulas and parameters. Both the
fresh c version and c+2 version pass. A finite semantic negative control shows
that allowing a matrix parameter to equal its binder label captures it and
can change the schema's truth value. These are finite syntax/semantic tests,
not a formal proof for arbitrary matrices. The bound argument above explains
the general adapter. It still needs a Lean syntax/proof-calculus bridge.

## Two different formula codings

The base3 measurement retains `Imp=3P`, `Rel=3P+1`, `All=3P+2`, with
code1=Rel(0,0) as a relative falsity alias. Its correctness still needs the
separate alias/capture argument. Optional irreflexivity is measured as a
separate emitted row; adding it does not establish logical completeness.

The primitive-Bottom control uses

```
Truth = 0; Bottom = 1
Imp(A,B) = 4P(A,B)
Rel(i,j) = 4P(i,j)+2
All(i,A) = 4P(i,A)+3.
```

Every residue1 code denotes Bottom; in particular code5 is an alias of code1.
Numerical encode-after-decode identity or injection is therefore **not**
claimed. The decoder interprets code0 as Truth rather than recursing through
its Imp(0,0) numerical collision. Canonical re-encoding followed by decoding
preserves the decoded formula. A 100000-code test checks that normalization
roundtrip and the strict variable-label bound. The latter follows generally
from the elementary Cantor-pair bounds and decreasing child codes.

Only formula constructor references are retagged after code sharing. The old
+2 `wal()` helper implements Rel; the old +3 `weq()` helper implements All.
Historical state names do not indicate an equality operation. Implication,
code1, the NIP comparison target, proof/list pairing, enumerator and nine-register
order are unchanged. All225 small register-level constructor contract cases
pass. None of these checks proves a full unbounded binary simulation.

## Measured costs and sharing

Original rho6, GEN, rho8, QI, commutation and freshly gated atomic membership
vacuity remain. GEN reads the previous cache before the normal parameter read.
The unchanged vacuity gate and register cleanup remain separate from PSC.

| Variant | Decision | Framework | Working |
| --- | ---: | ---: | ---: |
| PSC with separate c≥2 gate, base3 | 199 | 62 | 261 |
| Fresh k=c+2, base3, first row order | 194 | 62 | 256 |
| Fresh k=c+2, primitive Bottom, first order | 195 | 62 | 257 |
| Fresh k=c+2, base3, best row order | 193 | 62 | 255 |
| Fresh k=c+2, primitive Bottom, best order | 194 | 62 | 256 |
| Primitive Bottom plus separate IR, first order | 201 | 62 | 263 |
| Primitive Bottom, raw-word Re-Pair seed93 | 190 | 62 | 252 |

The first logical order after GEN is rho8,QI,Comm,original-rho6. The best order
is original-rho6,rho8,QI,Comm. All24 row orders and both relative-conjunction
orders were compared with separate PSC/vacuity rows; the separate rows win.
Weighted Re-Pair on the entire unparsed macro word, seed93 and exponent4,
then backend sharing gives the final252 measurement. Among200 seeds, one
reached252 and twelve reached253; these are selected-family measurements,
not minimality claims. The algorithm follows source08's exact-word grammar
idea, implemented here over the new emitter. The exact expanded macro word
is checked before and after sharing. All19 macro roots have zero statically
escaping break/continue levels; added top increments also escape no control.
Thus ordinary reassociation of these helpers preserves their register behavior,
although the Python checker/compiler is not Lean-verified.

The final named table has503 rows and only the public backend's missing
`1.inc/read1` transition. Its SHA256 is
`76af4b702bc455bb4560530476b1c82313aa12d44cd4757c5aed2bf11710a08c`.
It is generated outside the repository as `offset_bottom4_repair93.tm`.
No new total literal table or replacement of the earlier frozen252 artifact
is installed. Generic missing-row normalization is covered separately by
`PartialTotalization.lean`; no new table correspondence is inferred here.

## The actual logical obstruction and its scope

Interpret implication by Boolean implication, all membership atoms as false,
Truth as true, Bottom as false, and **every universal quantifier operator as
constant true**. Generalization preserves validity. Rho8 is a propositional
tautology, QI and commutation hold, and original rho6 holds because its
existential antecedent is false. Atomic membership vacuity holds. Every PSC
instance is true: its premise and its outer universally quantified conclusion
are true. The separately emitted IR row is also true.

Yet `All(a,Bottom)→Bottom` is false. Hence this very PSC/logic skeleton cannot
be a complete ordinary first-order calculus. This is an algebraic proof-system
counterinterpretation, not a nonempty membership structure satisfying genuine
first-order PSC. It does not challenge the accepted mathematical consistency
calibration. Adding same-variable specialization would reject this particular
counterinterpretation but would not by itself prove adequate renaming,
substitution or first-order completeness. That repair is not implemented here.

Crucially the same interpretation **does not model the actual C/G bundle of
the earlier frozen252 experiment**. Directly evaluating all retained rows for
all32 Boolean payload assignments gives valid logical rows and V=true, but
C=false and G=false: both have outer **existential** quantifiers. Therefore
V∧(C∧G) is false. The executable negative control prevents using this new
PSC obstruction to make a stronger claim about the old candidate. Its
calibration remains unresolved for the reasons already documented, including
the separate dual-rho6 gap. No unconditional machine-nonhalting claim follows.

## Reproduction

The unchanged pinned upstream is `297ab8df7e5de329605c3875b4934643b371a5e3`.
The script reuses the authored `recover_wade_dag.py` and template-emitter
interfaces and copies Andrew Wade's MIT-0 backend, with its license, only to
outside scratch. It never modifies the import or the core experiment. Run
without `-O`; entrypoints reject assertion-disabled execution.

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.py \
  --scratch /tmp/zfc-psc-reproduce --output-evidence /tmp/zfc-psc-results.json
```

That fast recipe regenerates seven fixed variants and runs the adapter,
normalization, constructor and actual-bundle controls. Add `--search` to repeat
the24-order/grouping comparisons and200-seed family recorded in
`psc-backend-results.json`. Generated named machines remain in scratch.
No Lean build, end-to-end proof, new busy-beaver bound or solved goal is
claimed by this checkpoint.
