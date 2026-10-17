# Freshness for every original four-tag code

`DecodeFresh254.lean` supplies a finite ingredient for the missing reverse
numerical calibration. It imports the actual `Code254` definitions and applies
to every natural code, including codes outside the named encoder's image.
It concerns the attributed Mira-Cult/Jeff/mira-emmy original frontend, not the
different base3 or primitive-Bottom experimental encodings.

For positive c, every bound or free label in `Code254.dec c` is smaller than c.
The proof works by induction on the actual fuel decoder. Even an exhausted
fuel branch introduces only label0; every recursive nonzero-code argument is
at most a component of the unpairing of c/4, strictly smaller than c. This also
covers arbitrary nested zero codes. The concrete examples are

```text
dec 4 = Imp(Rel(0,0), T0)
dec 8 = Imp(T0, Rel(0,0))
T0    = Imp(Rel(0,0), Rel(0,0)).
```

Zero is a necessary exception to syntactic freshness: `Free 0 (dec 0)` holds.
Its interpretation is nevertheless always true. Consequently the semantic
support theorem is uniform: environments agreeing on labels strictly below c
give the same truth value to `dec c`, including c=0. Updating any label at least
c is harmless. In particular the auxiliary update at c can be ignored beneath
arbitrary subsequent input/output updates, with no irreflexivity assumption.

This does not change the actual bundle gates `c ≠ a` and `c ≠ b`. The semantic
matrix lemma holds for arbitrary a,b, but the calculus still emits the same
gated bundles. The a=b collision cases in the whole C/G wrappers remain
separate obligations. There is no claim that `enc (dec c) = c`: the named
encoder is always positive and can replace zero children by nonzero codes.
The relative falsity code1 remains `Rel(0,0)`; it is false under every binder
only in a globally irreflexive model. Choosing one loop-free value for name0
does not establish that property after arbitrary `GEN 0` updates.

The new `QuotientZF0` direction has been independently read: a ZF0 refutation
rules out every nonempty irreflexive EncBundle model via its CP/GIC quotient,
so the existing completeness theorem gives `C254 F`, then the abstract
enumerator halts. Its contrapositive is abstract nonhalting implies Con(ZF0).
This proof does not assume that every EncBundle model satisfies all decoded
bundles. The opposite direction still needs a construction or proof translation:

```text
Con(ZF0) → a nonempty irreflexive model of every actual decoded gated bundle
         → ¬ C254 F.
```

`model_of_BCon` currently supplies a ZF0 model and a valuation, not that richer
decoded-bundle model. `psc_of_zfAxioms` supplies subset-bounded supported PSC,
using `SetLike` and the actual definable closure theorem; it is not an
unrestricted GIC/Collection theorem or an IR theorem. Native equality in decoded
matrices also requires care: `ProfileModel.ModelsGIC` only quantifies over
equality-free matrices. The independently identified twin-universe obstruction
prevents simply treating that equality-free interface as all decoded bundles.
An actual named-form translation, suitable collection/faithfulness resources,
and the positive-code/zero-code split above are separate ingredients.

`NamedNumeric254.Q f := NumThm (encode f)` does not remove this gap: asking for
a model of all Q axioms already asks for soundness of every numerical theorem.
Its checked refutation equivalence is a proof adapter, not an independent
set-theoretic construction. The pinned upstream reverse route uses the
well-founded-part and constructible-class interpretations in `S_sound.v`,
including reflection for CP and least-stage collection for GIC. Those
interpretations and their exact local formula/schema bridges remain to be
ported; see `foundation_choice_route.md` for the separate Foundation/Choice
refutation comparisons. No machine, compiler or state count changes here.

The 130-line module compiles with the explicit pinned Lean4.32.0 compiler
in 0.65seconds. All11 theorem axiom audits and three callers pass. The
callers retain zero's syntactic free occurrence while applying semantic
invariance, eliminate an existential auxiliary update under arbitrary
input/output updates, and check the unequal re-encodings
`enc (dec 4) = 676`, `enc (dec 8) = 616`. Dependencies are limited to
`propext` and `Quot.sound`; the two concrete decoder equalities are axiom-free.
No admissions, custom axioms, native evaluation or upstream Coq build is used.
The source-verified dependency cache is reused, so this is a scoped module
check rather than a fresh rebuild of the complete proof closure. Exact
commands and results are in `results/decode-fresh254-verification.json`.
An independent full source read found the occurrence bound, zero exception,
semantic support and arbitrary-label update scope correct.


The subsequent `NativeDecoded254` supplies the native matrix/collection
adapter described above, including the allowed binder collision and truth-zero
cases. It also closes EncBundle versus decoded-bundle model equivalence
under raw IR and an explicit valuation. The separate quotient-IR and
Foundation/Choice problems remain; the freshness lemma alone never asserted
those consequences.
