# Lean source review: a shared guarded-subtype interpretation

Pin: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6` of VladimirReshetnikov/ProveIt.

## Decision

Do not adopt the supplied generalized kernel solely to shorten today's K215 proof.
It exposes a real duplicated semantic argument and has a sound mathematical
specialization to the two current De Bruijn translations, but the complete
draft's maintenance cost does not justify a source-size claim. Keep it as a
conditional reuse design, for example if another parameterized subtype
interpretation is added. A smaller local quantifier-transfer helper may be a
better fit for two clients; no such smaller patch is claimed here.

Nothing in this directory was compiled with Lean. No repository file was edited,
and no upstream program, generator, or proof source was executed. Only the two
owned Python audits were run. Their results establish source integrity and finite
regressions, not the quantified theorem or a fresh K215 endpoint check.

## Current implementation status

- The direct FullSeed route is implemented in the actual production endpoint:
  `KEndpoint.c222_of_zf_refutation`, line 37, imports `KSeedDirect222` and uses
  `fullSeed_direct_of_derivable`. Do not propose the old first-quotient removal
  as an unimplemented new contribution.
- `KQ1Replacement.replacementChoiceForm`, line 37, still embeds
  `KQ1Model.translate phi`; its `quotient_replacement`, line 103, still takes
  the raw-matrix / representative route. Native quotient Replacement is an
  existing proposal, not new here. The `collection-first` packet additionally
  reports a checked native Separation/Replacement and WF reuse component.
- The existing `proof-boundaries/direct-infinity` proposal reports checked
  serial-seed, tagged, and quotient adapters, while explicitly leaving the
  production interface and complete endpoint integration open. Direct Infinity
  is therefore not a new recommendation of this review either.
- The existing `common-macros` packet already proposes checked envelope and
  comprehension sharing across `KLowerTag` and `KLowerQHyp`.
- Phase15's recorded build is historical evidence for its selected source bytes.
  It cannot certify these new drafts. This review does not infer a current
  kernel check from commit prose, the earlier receipt, or successful Python tests.

The accompanying source audit verifies two actual import paths:

1. `KEndpoint215 -> KEndpoint -> KLowerQHyp -> KLowerEqv -> KLowerTag -> KLowerRel`.
2. `KEndpoint215 -> KEndpoint -> KLowerQHyp -> KQ1ZF -> WFModelCore -> WFRelativization`.

These are witnessed paths to the target files, not a complete endpoint closure
census. No module-count, complete-source-closure, build-time, or kernel-term saving
has been measured.

## The genuinely common argument, with exact boundaries

The two source languages really are the same eight-constructor `SetTheory.Form`
with De Bruijn indices. Their ambient membership is unchanged, and their target
membership is ambient membership restricted to a subtype. Equality remains
native Lean equality; it is not `Profile.Same` or coded bisimilarity.

1. `KLowerRel.relT`, lines 28-36, inserts the raw marker at slot d. Its `sh d`
   leaves slots below d untouched and moves all other slots by one. A quantified
   variable is guarded by `fMem (d + 1) 0`, and the body uses context d+1.
   `KLowerRel.sat_relT`, lines 54-74, carries both the `Shows` invariant and
   `rawEnv d = marker` through the induction.
2. `WFRelativization.translate`, lines 28-36, leaves every variable slot in place.
   Its bound variable is guarded by the ambient `wfForm 0`. The guard is NOT
   recursively translated. `WFRelativization.sat_translate`, lines 63-112,
   repeats the subtype equality and quantified-witness argument.

`ConstructibleReflect.relT`, line 72, instead targets `NamedZF.NForm`, allocates
fresh names, uses named updates, and requires the slot-freshness condition
`forall i, s i < f`. Its `nsat_relT` at line 82 is outside the present reuse claim.
`ConstructibleZF.sat_sub` at line 154 is a genuinely generic class/subtype semantic
lemma, but it is currently located downstream of constructibility. Importing
that module into the lower chain would be the wrong dependency direction.
It is NOT deleted or replaced by the present draft.

## Exact reusable interface

`GuardedSubtype.lean` introduces a context C, an update next : C -> C, a variable
map slot : C -> Nat -> Nat, and an ambient guard formula guard : C -> Form.
The guard is evaluated after the new quantified variable has been pushed.
The syntactic translation leaves the guard itself unmodified.

For a fixed predicate P and invariant Good(c, rawEnv), the sufficient obligations are:

1. slot(next(c), 0) = 0.
2. slot(next(c), i+1) = slot(c, i)+1.
3. Good(c, rawEnv) implies Good(next(c), scons x rawEnv).
4. Under Good(c, rawEnv), `Sat mem (scons x rawEnv) (guard c)` iff P(x).
5. The initial environments agree at mapped slots:
   rawEnv(slot(c,i)) = (subEnv(i)).val.

Then ambient satisfaction of the translated formula equals satisfaction in
`{x // P x}` under induced membership. The supplied proof draft performs one
formula induction. Equality uses `Subtype.ext` and `congrArg Subtype.val`.
The quantifier steps construct a subtype element only after proving its guard.

There is no inhabitant assumption, representative selection, Classical.choice,
Extensionality, Foundation, irreflexivity, or set-theoretic collection premise.
An empty subtype creates no problem: the statement already quantifies over a
valuation into that subtype, which cannot exist if it is empty. Invariant
stability is stronger than strictly necessary (it is required for all raw x),
but both concrete adapters satisfy it definitionally, without a model axiom.

## Specialization and preservation obligations

Tagged specialization:

- C = Nat; next = Nat.succ; slot = KLower.sh.
- P(x) = mem marker x.
- Good(d,r) = (r d = marker).
- guard(d) = fMem (d+1) 0.
- The two slot equations are elementary arithmetic/case facts. Pushing an
  arbitrary variable preserves the marker equation at the incremented index.

WF specialization:

- C = Unit; next = identity; slot(_,i) = i.
- P(x) = WellFoundedPart.WF mem x; Good = True.
- guard(_) = WellFoundedPart.wfForm 0.
- All slot/invariant laws are reflexive, and the guard law is exactly
  `WellFoundedPart.sat_wfForm`.

The Unit context is deliberate. Using a growing Nat context for WF would make
the irrelevant depth show up in recursive terms and demand an extra invariance
lemma. The tagged and WF bodies have opposite public iff orientations;
the tagged public wrapper must take the symmetry of the generic theorem.

Dependency direction is strictly syntax -> shared kernel -> concrete clients.
The core imports only `FirstOrder.Fol`. A production version would live in a
fresh lower-level module imported independently by `KLowerRel` and
`WFRelativization`; neither concrete client would import the other. The supplied
comparison module imports both old clients only to state compatibility tests.
It must not become a dependency of either client, since that would be cyclic.

`GuardedSubtypeAdapters.lean` is a comparison client against unchanged old source.
It includes uncompiled proofs of exact formula equality for ALL formulas,
`tagTranslate_eq` and `wfTranslate_eq`, not merely equisatisfiability, and the two
semantic instantiations. Its formula equalities use explicit constructor
congruence, not an unverified unfold/refold simplifier cycle.

For any later adoption, preserve the old qualified declarations and these types:
`relT`, `Shows`, `shows_scons`, `sat_relT`, `sat_top`; `translate`, `liftEnv`,
`liftEnv_scons`, `envOfWF`, `liftEnv_envOfWF`, `sat_guard`, `sat_translate`,
`sat_translate_of_wf`, `sat_translate_scons`, `sat_translate_matrix`,
`sat_translate_relOf`, `equalityFree_translate`.
The last theorem must continue to prove an iff, since the equality-free guard
does not introduce or erase equality atoms in the original formula.

## Honest cost accounting

The standalone core is 108 physical lines. Its full comparison client is 71
physical lines. They add 179 lines of draft source as delivered; neither file
has replaced production source. These counts include comments and blank lines.

The two old translation definitions and their main satisfaction proofs together
occupy 89 lines: tagged 9+21, WF 9+50. Even additionally retiring the tagged
`Shows` definition (2) and `shows_scons` proof (8) yields only 99 target lines,
before restoring public adapters. The 108-line core alone is larger than that
entire direct target. Deleting the comparison identities from a production
import path would not erase their validation/maintenance cost, and the comparison
client depends on the original declarations, so it is not a deletion patch.

Consequently this is NOT demonstrated proof shortening. One shared semantic
induction is an architectural benefit, but fewer inductions do not imply fewer
maintained lines, smaller kernel terms, or faster checking. The main review
should prioritize the independent checked-data structural recommendations and
existing integration opportunities over this optional abstraction.

## Validation performed and still required

Executed locally:

- `python -I -B audit_sources.py --out SOURCE_AUDIT.json`
- `python -I -B check_guarded_subtype.py --out FINITE_CHECKS.json`

The first verifies 49 frozen source files against their returned Git blob SHA-1,
also records SHA-256, checks the exact declaration locations, and checks the two
import path witnesses. It also reproduces the physical-line cost comparison,
including both complete draft files and the exact old declaration ranges.
With `--repo PATH`, it additionally compares a supplied
checkout's source bytes read-only. It does not invoke Git or Lean.

The second checks 162 formulas on 36 finite membership structures (all 16
two-element structures and 20 sampled three-element structures), makes 972
syntactic-equality comparisons, and independently checks the finite predicate
used by the copied WF guard. It finds counterexamples for each deliberately
broken translation: frozen marker index, omitted variable shift, and replacing
native equality with predecessor-profile equality. The JSON records the full
counterexamples. These are finite regression tests, not a quantified proof.

Before any adoption:

1. Check the core and comparison clients with the repository's exact Lean
   toolchain and dependencies. Put this directory on LEAN_PATH only as a
   research module root, never ahead of production copies under the same names.
2. Compile exact unchanged typed clients of both old interfaces, including all
   unary/matrix/Replacement conventions and equality-free preservation.
3. Inspect axioms of the new kernel and adapters. The mathematical kernel needs
   no new axiom; a tool output must establish the actual elaborated profile.
4. If replacing definitions, verify exact syntax equality and update dependent
   simplification lemmas, not just final semantic statements.
5. Rebuild both affected paths through `KLowerQHyp`, `KQ1ZF`, `KEndpoint`, and
   the actual `KEndpoint215` / compatibility clients. Check any alternate
   import path before claiming a source-closure saving.

No build, size, runtime, or ZFC internalization claim is supplied by the finite audit.
