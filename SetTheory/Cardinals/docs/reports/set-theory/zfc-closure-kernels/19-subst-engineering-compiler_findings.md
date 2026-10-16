# Compiler findings at ProveIt 47f3a360

## 1. A 268-state control retaining the original logical system

The selected result has 268 working states, 206 decision states and 62 Wade
framework states. Its numeric table has 536 transition rows, start state 0,
and terminal target 268. Its SHA-256 is
`77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d`.

This is a one-state improvement over the supplied 269-state rebracketing of
the full original program. It is not a record and remains above the verified
253-state baseline. It uses the existing Andrew Wade backend rather than the
more compact interpreter of the published benchmark.

Unlike the 248/250/252 equality-free candidates, it keeps every one of the
original eight logical rows, their order, their scalar parameters, original
rho6, both equality congruence rows, equality existence, equality Euclideanness,
both gated atomic vacuity formulas, the original base-four codec, and all
enumerator and arithmetic helpers. No logical schema is deleted or dualized.

Write the published four theory factors as C,G,Vr,Ve. The source changes are:

1. In C, commute the local power-container and transitivity conjuncts; call
   the result C*.
2. In G, commute the outer collection and support conjuncts; call it G*.
3. Replace `(C & G) & (Vr & Ve)` by `Vr & ((Ve & C*) & G*)`.
4. Apply the supplied weighted Re-Pair algorithm, seed341, exponent4, retaining
   the existing closed macro161 (`push-a; implication`) before grammar search.

These are propositional rewrites under the original quantifiers. For the
actual relative conjunction,

    And_F(A,B) = ((A -> (B -> F)) -> F),

Boolean evaluation is `F or (A and B)`, so commutativity and associativity are
classical implicational tautologies even without assuming F false. Original
rho8 supplies implicational completeness. The original normality and GEN
rules lift provable equivalence through quantifiers; derived existential
quantification then also preserves it. Thus these rewrites require none of
the disputed equality-deletion or dual-rho6 arguments. A formal proof-code
translation and the binary interpreter theorem are not supplied here.

The fixed search examined exactly 53,760 variants:
8 C commutations x 4 G commutations x 24 orders of C,G,Vr,Ve x 5 binary
parenthesizations x 7 seeds x 2 exponents. The seeds are
341,181,122,93,39,240,1195; the exponents are2 and4. The smallest table in
this finite family has 268 states. This is not a global lower bound. A separate
60,000-step deterministic exploratory search allowing logical-parameter
permutations and row orders found the same selected table; that exploratory
search is not needed to reproduce the result.

### Register-program certificate

The certificate relates the generated candidate to an independently re-emitted
register program for exactly the revised axiom word. There are 4,533 reachable
operation pairs: 2,601 increments, 1,931 decrement tests, and one halt. Both
zero and positive decrement successors are checked. Both unfolded decoder
trees have 6,460 instruction sites, and every contracted control-only path
has at most four steps. The candidate has 206 decision nodes; the separately
re-emitted reference has 217.

The independent verifier uses the supplied `verify_rm_certificate.py` path
engine, which does not import the generator or binary compiler. It accepts
the certificate. A separate numeric parser checks all 536 distinct state/read
rows, symbols, directions, and targets. This proves a finite operation-level
correspondence when combined with the certificate theorem already in the
supplied report; it is not a proof of the Wade binary interpreter.

The table uses the prior explicit missing-row convention: the public engine's
undefined `1.inc/read1` row is filled by write1, move right, halt. This adds no
working state and preserves halting relative to partial-transition semantics.

### Selected files

* `full_logic_search.py` — deterministic generator/search.
* `full_logic_grid_run/full_logic_best.tm` — total numeric268-state table.
* `full_logic_grid_run/full_logic_best.named.tm` — named source table.
* `full_logic_grid_run/full_logic_best.dag.json` — candidate register DAG.
* `full_logic_grid_run/full_logic_reference.dag.json` — direct revised-word DAG.
* `full_logic_grid_run/full_logic_rm_certificate.json` — finite RM certificate.
* `full_logic_grid_run/full_logic_results.json` — recipe, source hashes and count.
* `full_logic_grid_run/independent_rm_check.json` — independent certificate result.
* `full_logic_grid_run/independent_table_check.json` — numeric format/count check.

Reproduce from the shared scratch root:

```sh
python compiler_work/full_logic_search.py \
  --repo ProveIt \
  --prior research_inputs/zfc_small_machines_20261016/zfc_small_machines_20261016/vendor/one_schema_machine \
  --output /tmp/full-logic-grid \
  --iterations 0 --conjunction-grid
```

The Re-Pair algorithm and certificate architecture are explicitly attributed
to the supplied one-schema research archive; they are not new here. The new
contribution is their application to the listed full-calculus propositional
rewrite and the resulting268-state control.

## 2. PSC costs with the original equality-bearing logical rows

`full_logic_psc_controls.py` retains all eight original logical rows and both
atomic vacuity formulas, swaps C/G for the fresh-k=c+2 PSC template, and measures
512 seeds at each exponents 1, 2, 4 and 8. Each row below therefore searches 2,048
grammar choices with a fixed logical-row order.

| Theory emission | Working states | Selected seed/exponent |
|---|---:|---:|
| PSC with root universal |278|29/8|
| PSC with free root |278|9/8|
| PSC plus irreflexivity |282|127/2|
| Free-root PSC plus irreflexivity |282|17/8|

The counts are exact for the emitted tables in this family. They do not prove
optimality or consistency calibration. The original relative-falsity base-four
codec remains; these are not a newly proved primitive-bottom first-order
checker. The free-root presentation is classically equivalent to its universal
closure in ordinary theorem logic, but its selected binary cost does not improve
in this search. The original calculus costs cannot be silently replaced by the
much smaller incomplete equality-free skeleton.

The source, JSON evidence, named and total tables are in
`full_logic_psc_controls.py` and `full_logic_psc_run/`. Reproduction uses the same
`--repo`, `--prior` and an outside-repository `--output`, plus `--seeds 512`.

## 3. A particularly small regression for the PSC logical defect

The newest supplied report already gives a finite-sort model that defeats both
C/G and PSC and survives same-variable specialization. The following is a
simpler PSC-only certificate, not a new obstruction consequence.

Interpret all universal quantifier operators as the identity on Booleans,
implication materially, Truth as true, Bottom/F as false, and

    Rel(i,j) is true iff i >= 2 and j = 0.

For k=c+2, all of R01,R0k,R1k,Rk1 are false and Rk0 is true. The emitted PSC
premise is therefore true; its guard is false; its closedness and support
clauses are true, independently of the truth value of the arbitrary matrix.
Every PSC instance is true. All retained old-rho6 logical rows, atomic vacuity,
and the optional irreflexivity axiom are true as well.

This model validates `All(i,A) -> A`, removing the root universal, and adding
any existential prefix. Those inexpensive changes do not repair the calculus.
But the ordinary first-order substitution instance

    All(2,Rel(2,0)) -> Rel(1,0)

is false. A complete repair has to connect the different variable positions,
for example by checked substitution/alpha conversion or the original equality
logic. Modal axioms alone cannot remove this identity-quantifier interpretation.

`psc_identity_model.py` checks the exact repository PSC AST, 128 Boolean
logical cases, 20,000 numerical matrix-code cases across the base-three and
primitive-Bottom codings, and 256 independent matrix-bit/binder cases. Its
general proof is the displayed constant-size Boolean calculation, followed
by induction on formal proofs. It is an algebraic semantics of the coded
calculus, not an ordinary first-order membership model. No compiler theorem
is assumed or asserted.
