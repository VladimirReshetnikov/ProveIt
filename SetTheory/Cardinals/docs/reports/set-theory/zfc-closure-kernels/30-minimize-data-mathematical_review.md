# Mathematical review of report sections

Reviewed 16 October 2026 by the theory-design subagent.

## Scope

Read every then-present section in
`output/zfc_minimization_20261016/sections`: `overview`, `target`,
`theories`, `support_obstruction`, `finite_presentations`,
`fixed_emission`, and `internalization`. The review addresses ordinary
mathematics, source interpretations and claim scope. It does not certify
the numerical compiler counts, rerun the compiler/search suites, or build
Lean/Coq.

## Findings and direct changes

No substantive defect was found in the regular-ordinal model theorem,
the satisfiable-EPR finite-model obstruction, the internal adequacy
proposition, or the independence assumptions. Four small corrections
were made directly in the report:

1. `fixed_emission.tex`: replaced “injective finite permutation” by the
   precise “permutation of variable labels with finite support,” with
   distinct input/output roles explicit. Corrected the provenance of
   `k=c+2`: it is this experiment's offset, not the original emitter's
   exact convention. The original emitter uses `c` itself. The rewritten
   paragraph derives offset freshness from the original decoder's
   free-label bound and its closed code-zero default.
2. `support_obstruction.tex`: expanded the club-closedness sentence into
   its actual supremum argument, removing ambiguity about “cofinal
   subsets.” All main model and consistency claims are unchanged.
3. `theories.tex`: distinguished the Russell-root construction giving
   functional Replacement from successor closure giving Infinity.
4. `internalization.tex`: made explicit the provably decidable finite
   proof predicate needed for the optional total general-recursive
   witness search. Ordinary primitive-recursive certificate codings have
   this property. The adequacy contract itself remains two existential
   witness implications and imposes no primitive-recursive runtime bound.

## Checked source details

Against the pinned vendored upstream source:

* `ZF/m254/coq/logic/Bundle254.v` defines the displayed BC/BG wrappers.
  The GIC occurrence of the output variable is correctly shadowed by the
  inner existential; the domain occurrence is outside that binder.
  Separating a numeric matrix code `c` from hull label `c+2` is a genuine
  change but has the stated ordinary first-order interpretation.
* `ZF/m254/coq/logic/Sound254.v:197`, `D_fr`, gives
  `fr v (D n)=true -> v<n`, including code zero via the closed-default
  branch. `Wff254.v:77`, `D_0`, identifies that default. Therefore `c+2`
  is fresh for every decoded matrix and is distinct from labels 0 and1.
  No altered-enumerator completeness theorem follows from that fact alone.
* `Comp_Bundle254.v:91`, `TB_IR`, derives translated IR from `thm_I`
  because `tau(not Rel00)=F -> F`. The report correctly adds no new IR
  runtime row while retaining the original relative translation.
* `Comp_Bundle254.v:208`, `TB_gic`, uses fixed roles1/3 in its translation,
  supporting the earlier fixed-nonlogical-label proposal. It does not
  directly certify this new0/1/offset emitter.
* `S_main.v:38`, `S0_equicons`, confirms the source claim for the theory
  without the separate IR sentence.
* `stdzf_r3/zfc/Z_main.v:83`, `ZFCReg_equicons`, has the orientation needed
  for the displayed composition with `iff_sym`.

## Important scope retained

The report does not promote external Coq closure/CI to a newly established
arithmetized ZFC endpoint. It also does not wrongly demand a serialized
primitive-recursive proof translator: an ordinary uniform set-model
argument or the two coded finite-adequacy implications suffice.

The EPR obstruction explicitly assumes the fixed presentation is
satisfiable. It does not misuse bare consistency to exclude every false
Sigma1 theorem. The nonhalting unprovability and halting unprovability
statements have their distinct hypotheses.

The fixed-label idea is credited as prior source09 work; the new claim is
the measured implementation. Its 283-state table is correctly called a
compiler experiment with remaining binary/runtime/frontend obligations.

No theorem of global novelty, state optimality, smaller-than253 calibrated
machine, or newly formalized internal consistency equivalence is asserted.

## Final machine-search and proposal review

Also reviewed `machine_search.tex` and `proposal.tex`, together with
`optimizer/deliverable/README.md` and the literal incoming-edge assertions
in `quick_verify.py`. The conditional budget arithmetic is correct:
252 - 62 = 190, 219 - 190 = 29, 221 - 190 = 31; framework costs 61--64
give decision ceilings 191--188. These are backend-dependent necessities,
not forecasts of an achievable saving.

Applied the following final mathematical/scope corrections:

1. Replaced the narrow local detour argument with the exact guard proof.
   The only incoming transitions to old49 are 34/0 and79/0, both writing
   zero and moving right. A blank initial49 reads zero. Thus every use of
   the changed49/1 has a zero on its left. Each of the three detours
   realizes one original step in exactly three steps without an
   intermediate halt or dispatcher visit. This proves the same blank-start
   halting behavior, and identical dispatcher configurations, for every
   initial working state. It is an ordinary proof, not a new kernel build,
   and does not calibrate that common behavior to Con(ZFC). Removed the
   unnecessary long-run observation from the argument.
2. Corrected startup-detector scope: it tests all header gaps >=40 and
   overapproximates legal frames by allowing arbitrary34 PC bits and
   register/spare values. A hit would still need a correct/cofinal
   refutation-search continuation. The proposal now identifies gaps37--39,
   different encodings/dispatcher conventions, and later times as untested
   directions; larger gaps were already covered.
3. Added the exact zero-only/first-write initial-state partition and made
   explicit that a finite symbolic-checker rejection is not a semantic
   impossibility theorem (500 abstract fuel units and symbolic limitations).
4. Restricted the support-obstruction implication to the actual weakened
   closure presentation and accompanying axioms proved to have the ordinal
   model. It does not exclude every alternative source of strength.
5. Made the proposed native PSC rule's immediate conclusion existential.
   A fresh hull name may be used only under the ordinary eigenvariable
   discharge rule, or with all dependencies in a separately justified
   conservative Skolem implementation. The unchanged captured matrix and
   environment remain part of the rule specification.

The environment and parameter-restriction proposals remain explicitly
conditional on sound binding/decoding and a noncircular tuple bootstrap.
No proof-system compression or state reduction is claimed from syntax
alone. LaTeX rendering, bibliography integration, and empirical reruns
remain with the parent/other agents.
