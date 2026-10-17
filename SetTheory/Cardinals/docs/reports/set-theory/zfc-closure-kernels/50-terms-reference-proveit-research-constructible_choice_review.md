An independent read-only review of all1661 current lines in `TransRec`,
`ConstructibleDef`, `Constructible` and `ConstructibleReflect` found no
concrete mathematical defect. The reviewed snapshot is commit
`337dd3cb25c1bb4ef47e7cb2e9b7bdfa7eeb6837`, including the newer695-line
reflection file. No Lean or Coq build was run by this reviewer. The complete
[audit record](results/constructible-independent-source-review.json) is retained
in the repository; full source snapshots and the longer review remain at
`/tmp/zfc-constructible-independent-jmcwdhl9/`.

The recursion uses definable internal ordinal induction. The closing
sequence ranges over the entire model omega; its ordinal-valuedness is
proved by an actual-Form `omega_ind` instance. Least witness-stage ordinals
are unique and collected by functional Replacement, so no Choice axiom in
the object model or external well-foundedness is assumed. Foundation is
explicitly supplied as `Regular mem`, and powersets are explicit premises.

There is an important prerequisite for the unfinished Choice proof.
`ConstructibleDef.DefinableIn` ranges over **all internal formula codes and
full internal omega-environments**. Even when a stage X has a well-order,
one cannot assume X^omega is well-orderable in ZF. A well-order of Def(X)
must first reduce each definition uniformly to an internally finite tuple
of parameters. The required next interface is an internal finite-support
theorem: for every `IsFormCodeSem H c`, some `n ∈ omegaV H` makes `SatIn`
invariant under replacing a genuine environment by another that agrees at
every internal index `i ∈ n`, for the same set-sized structure. This must
cover nonstandard codes too. It should itself have an actual formula
specification, allowing internal code induction and a definable least bound;
then it can support coding by well-ordered internal codes and finite tuples.
The eventual orders must be internal model well-orders, not an assumed
external `WellFounded` relation.

The existing `satIn_formCode` and `csat_ext_free` lemmas give the external
finite-support bridge for each fixed standard `Form`; they do not yet give
that uniform theorem for every internal code. This is an open interface,
not a refutation of any theorem in these four modules. Similarly, the
reflection theorem currently assumes the entire valuation is in its
reflecting stage. A later schema transport for an arbitrary valuation must
first replace it by one using only the finitely many free parameters.

These modules establish hierarchy, closure and reflection machinery. They
do not yet prove all ZF axioms in L, its definable global well-order, Choice,
or an arithmetic proof-code/PA comparison. No standard-ZFC consistency or
binary-machine endpoint is inferred from this review.

| Reviewed source | SHA256 |
| --- | --- |
| TransRec.lean | `c7e9caf6f59e1a6c9ef3a9cb7ac4c44f39ffb6fa882fbda7936b95fa718c784d` |
| ConstructibleDef.lean | `e487e6ff18b456c631ee377bafd7ddce998873686bea886723655f52ae07a699` |
| Constructible.lean | `c2d5ff0435d0e1f7bd5450c6f332999bbe887abfbc71a93deed46a7abc7bfa71` |
| ConstructibleReflect.lean | `07ad377189fdb57c73b0b9058c04820d2d03dfe3863406d1933ae03179cc7a15` |

A proposed route to the missing support interface is to prove existence
directly by internal formula-code induction. This is a plan, not a proved
lemma. Write `Agree(E,E',n)` for agreement of `applyV H E i` and
`applyV H E' i` at every internal `i ∈ n`. Write `Supports(c,n)` for the
uniform statement that this agreement preserves `SatIn H A R c` for every
`IsSetStructure H A R` and both genuine `IsEnvOn H A` environments. Apply
`LeanProofs.BoundedZFCConsistency.isFormCodeSem_ind'` from
`FormulaClosedSet.lean` to the definable property

```text
P(c) := IsFormCodeSem H c ∧ ∃ n, n ∈ omegaV H ∧ Supports(c,n).
```

The code conjunct supplies the child-code hypotheses required by the Tarski
clauses. The property must have an actual `Form` specification; merely
describing it as a semantic predicate does not discharge `isFormCodeSem_ind'`'s
`hdef` premise. Existing `ConstructibleDef.isCodeF`, `envOnF`, `satInF` and
their `nsat_*` specifications provide several of the needed pieces.

For either atomic constructor, a successor of the greater internal variable
index bounds both arguments. Falsity needs the zero bound. For implication,
conjunction and disjunction, use a common upper bound of the two natural
supports. For either quantifier, even the child's bound is sufficient:
`nat_zero_or_succ`, `econs_zero`, `econs_succ` and internal natural
transitivity show that consing the same bound value onto two agreeing
environments retains agreement below that bound. `econs_isEnvOn` supplies
the shifted-environment premises. The existing `satIn_memAtom`,
`satIn_eqAtom`, `satIn_bot`, `satIn_imp`, `satIn_and`, `satIn_or`,
`satIn_all` and `satIn_ex` clauses then reduce each constructor to its
children. All these steps must cover internal nonstandard indices, not
external finite induction on natural numbers.

This route would supply an existential internal natural support without
first constructing a recursive support function. A later definable least
support can use the uniqueness of a least natural bound. The further tuple
coding and internal well-order arguments for Choice would still remain.

A subsequent separate review of the404-line `ConstructibleZF.lean` at
`a856bfa0eb` also found no defect. It proves `L_models_ZF` with the actual
`InL` subtype and the ambient ZF, Power and internal Regularity premises.
Its Separation argument explicitly truncates arbitrary valuations to the
finitely many relevant parameters before applying reflection; thus that
caller obligation above has now been met. Replacement uses an actual
`InL`-guarded functional graph and the correct output0/input1 convention.
This fifth module supplies all ZF axioms in L, while the uniform internal
finite-support prerequisite for its well-order and Choice remains separate.
The [new review record](results/constructible-zf-independent-source-review.json)
retains its SHA256
`8d6802f21c12b9e31b8a7ba2738200cabbc5b8ce73cb9cd4bfe40663ef40b76c`.

A later root replay freshly checked all ten new modules in this dependency
closure (five set-code/satisfaction modules and five constructibility modules)
and seven axiom reports, including `L_models_ZF`. All passed with only standard
Lean axioms. [The fresh-check record](results/constructible-fresh-verification.json)
and [142-unit integration](results/theory-code-integration-verification.json)
retain exact source identities and scope; the original source reviewers did
not run these checks. This establishes the ZF model, without claiming Choice.

The proposed uniform-support interface is now implemented in the merged
`SatSupport.lean` from `f7844da33f`. A separate read-only review of all193lines
found no defect: `supF` is an actual formula for the induction predicate;
`isFormCodeSem_ind'` covers every internal code; environment totality and
functionality are explicit; and the quantifier step uses internal natural
predecessors and transitivity, without external induction on nonstandard
indices. The carrier has the stated `IsSetStructure` premises. “Finite” here
means internally finite: the support bound can be a nonstandard member of
the model's omega.

A fresh check of this module, the merged154-unit umbrella, six axiom reports
and four direct callers passed, reusing152 source-matched dependencies from
the completed153-unit binary closure. The
[support integration record](results/sat-support-integration-verification.json)
records the exact source, commands and caller statements. This closes the
support prerequisite identified above. Internal well-orders, constructibility
absoluteness and the final Choice comparison remain open.
