# Actual C222 full-seed source image: author receipt

26 October 2026. **Author fresh pair PASS; independent acceptance pending.**
Author: circuit_reduction. Main 721 lines; Checks 85 lines. Both complete
sources, all later changes, and the preparation/build/freezing drivers were
read before their respective execution. Only these new proof sources and
owned evidence files were written. No accepted source, shared object,
shared documentation, equation artifact or Git state was changed.

The final `typed_fullSeed_witness` proves, for every arithmetic model with
the stated IΣ1/IΣ2 instances, every internal `p` with
`IsSemiformula ℒₛₑₜ 2 p`, every free environment `F`, and every
`StreamFree s F`,

```lean
∃ d : V,
  ArithmeticHistory222.value d = encode F 0 s (fullSeedBodyVal p) + 1
```

This uses the actual current C222 history and encoder. The matrix code may
be internally nonstandard; the theorem is not restricted to standard
quotes. There is no supplied source-axiom image, matrix compatibility,
full-seed assumption, or semantic completeness premise. The final requested
stream has no oddness, disjointness, or size restriction beyond the explicit
free-parameter safety condition.

## Literal source binding

`fullSeedBodyMeta`, `fullSeedBody`, and `fullSeedBodyVal` are respectively
meta-level, internally typed, and raw-coded versions of the same body.
`fullSeedBody_quote`, `fullSeedBodyVal_eq`, and `fullSeedBodyVal_quote`
prove exact syntax/code equalities. With matrix slot0 = output and slot1 =
input, the literal body is:

```
∀ A ∃ C,
  (∀ y, y∈C → ∃ x,
    Q(x,y) ∧ ∀ x',
      (∀ w, w∈x' → w∈y) →
      ∀ y', Q(x',y') → ∃ z, Q(x',z) ∧ z∈C)
  ∧
  (∀ y, Q(A,y) → ∃ z, Q(A,z) ∧ z∈C).
```

All five matrix copies are bound explicitly:

| Copy | Source depth | Replacement vector |
|---|---:|---|
| Collected member's support | 4 | `[1,0]` |
| Closure request premise | 6 | `[0,1]` |
| Closure request witness | 7 | `[0,2]` |
| Root request premise | 3 | `[0,2]` |
| Root request witness | 4 | `[0,3]` |

The subset test at depth6 is `mem(0,1) → mem(0,3)`. Closure witness
membership uses `(0,5)` at depth7; root witness membership uses `(0,2)` at
depth4. The free environment is unchanged throughout. Source implication is
NNF-coded and is compared to numeric implication using the accepted actual
`encode_neg` theorem; no definitional identification of those two encodings
is assumed.

## C222 construction and freshness

`bounded_seed_pair` retains the entire
`ex c (conj (clos a b c P) (req b c P))`. Its proof uses actual guarded seed
pair gates, numeric padding equivalence, matrix congruence and existential
monotonicity. It never takes the weaker `imageBody` projection.

The generic `encode_stack_relabel` handles same-parity and overlapping
streams through an opposite-parity intermediary above `F+B+B`. Two-stack
matrix congruence similarly chooses an intermediary above `F+B+B'`, retains
both complete stack lengths, and discharges the actual `eindContext` from
the two input/output Eind certificates. Thus freshness is not inferred
from only the displayed endpoint labels. `matrix_vac` is the actual typed
encoder vacuity theorem with its environment, stream, and slot conditions.

Finite private `Frame` and `Layout` records organize this binder proof.
Their concrete instance is constructed from those matrix congruence and
vacuity theorems. They are not final theorem premises and do not contain a
source-image or full-seed field. Native shadowed binders are moved from the
inside out. Each change supplies both cross-body vacuity certificates and
an actual C222 Eind congruence. The proof uses `weq → Eind` where the actual
ALL gate requires it; it never asserts the reverse or identifies primitive
numeric equality with the interpreted source equality.

For a canonical odd stream, role labels are `s,s+2,...,s+12`; the matrix's
own binder stream begins at `s+14`. The encoded matrix uses the exact stack
`[s+4,s]`. The numerical padded label uses bound
`F + code([s+4,s]) + (s+14)`, so it exceeds every role and both complete
environments. Its even parity avoids the entire odd matrix stream. These
facts prove its typed-matrix vacuity and permit replacement by the source
container role. The root universal is then obtained by actual C222 GEN.
Finally, the complete source formula is relabeled to the caller's arbitrary
free-safe stream. No self-body vacuity is assumed for a shadowed binder.

The finite binder algebra itself uses IΣ1 C222 contracts. The typed
matrix/negation/alpha steps explicitly invoke the accepted IΣ2 results.
The final theorems retain IΣ2. They do not turn a standard semantic theorem
into an internal source-proof oracle.

## Checks, limits and provenance

Checks retain both native conjuncts; bind typed/raw/meta source syntax;
expose an arbitrary internal matrix history witness; retain parameter17
under a source binder; and test overlapping streams, the actual even stream
2 with empty environment, and truth/falsity matrices. All 17 axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. These are Lean
metatheory dependencies of C222 witness theorems, not added HA proof rules.

This packet proves the literal full-seed **body** images. It does not yet
supply a theory membership recognizer with arbitrary parameter closure,
raw CP/GIC images, tagged Collection, quotient/bisimulation interpretation,
full source-ZFC `AxOK`, runtime215 interpretation, or the HA equation
endpoint. The new source body is explicitly named here; no unimported
historical theory FQName is claimed to be definitionally identical.

The only main imports are `ValidatorSeedPadding222`,
`ValidatorSourceNegation222`, and `ValidatorExistentialRules222`. The private
provider `/tmp/validator-source-full-seed222-author-m7w5l6ru/lib` reuses 166
authenticated current-source modules, including 117 Foundation modules,
517 object artifacts and 40 explicit external boundaries including Init
and meta Aesop. The accepted independent SeedPadding provider is selected.
The earlier qualification on two Foundation SetTheory companion groups is
retained: present companion hashes are not retrospective historical
captures. No Foundation/dependency module was rebuilt; this is scoped
reuse, not a fresh whole-closure certification.

Only the new main/Checks were compiled with pinned Lean4.32,
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, `LEAN_SRC_PATH` unset,
and a 512MiB disk reserve. Outputs are new private regular files; cached
symlink targets were not overwritten. Final timings were 17.706/2.756s,
with empty main output and no final diagnostics. The final run records
2192 pre/post authentication observations and retains 776 inherited audit
observations; freezing rehashed both collections.

All twelve compiler attempts are preserved: nine failed attempts, two
intermediate main-only passes, and the final passing pair. Development
errors concerned local typed notation, quote/value equalities, cast/API
names, and one Checks namespace omission. A fixed quotation expansion hit
the default heartbeat limit; a separate exact `seedSubset_quote` lemma
resolved it without increasing any cap. The failed Checks run produced
Lean error-recovery `sorryAx` reports and exit1; it supplied no accepted
object. The earlier read-only audit's metadata TypeError and corrected
script are preserved separately. No sorry/new axiom/native_decide appears
in the accepted sources or final reported dependencies.

- Main source: `d3c667ea9d23f0e7e91975bd2967eb8c9c2ebee9b9bb5f4e849430dc81b39c04`.
- Checks source: `e38ea39117a2db1d5811bab77c4bd05a7bc4f70bd82aa916c1f87504adde6911`.
- Main object: `47bf6d5008afd6356e89a061edee902b728507414feb21d5220b662892e8c9d4`.
- Checks object: `f84b260c5c8fd4c8c425c2df9d0590ccc5b7cf340ace82ca272cb131c333dc62`.
- [Cache inventory](validator-source-full-seed222-cache.json): `83c4a8f969e6b54d06bc1db7c77541a5b367b6672a2cefd25db92c9bf7022f39`.
- [Replay summary](validator-source-full-seed222-replay.json): `30887bb85237ee408cac2dc7e27e92a4383d2a42c025635032b7df7c0561f1d2`.
- [104-file manifest](validator-source-full-seed222-author-replay/FILES.json): `3540c94c56597e7217b88660c7f47df965b60d8c3ecc4fd7dc9e1a555977aeaa`.

The approved plan and source/object pins remain frozen in
[the read-only proposal](../research/validator-source-full-seed222-plan.md).
