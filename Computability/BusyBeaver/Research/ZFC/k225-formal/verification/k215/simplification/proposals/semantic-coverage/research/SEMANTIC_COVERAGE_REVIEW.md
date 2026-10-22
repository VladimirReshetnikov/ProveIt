# Independent source review of semantic coverage

Reviewed against ProveIt `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.
Reviewed candidate SHA-256:
`d5b5f502c3ea0529d9c2aaf26a33d13d65e9f91a6da2cb4b3c774a9c2ac5dcd7`.

## Conclusion

No blocking logical defect found. The semantic interface is sufficient for the
same simulation argument; the old public API is retained. This is a source
and evidence review, not another independent compiler invocation or a rebuild
of the complete K215 endpoint.

## Specific checks

- `RunContract` uses `Reach1`, whose definition is a successful run of length
  `k+1`. No zero-length simulation has been substituted.
- Every `EdgeContract` keeps the path bound. Increment and decrement retain
  register-index bounds. Decrement has separate zero and positive branches,
  with the existing `Valid` guards and exact successor configurations.
- The target contains the full `conc` configuration with the existing PC,
  gap/overflow and register/spare representation. It is not a statement about
  only a local tape window or the control state.
- `.node` has contract `False`, so decoder failure cannot silently be
  reclassified as an intended halt. `Semantic.sim_stop` still distinguishes
  actual halt edges from the other cases.
- `HaltContract` is conditional on state 230 having no transition. Its use is
  not a vacuity loophole: `Semantic.sim_halt` and `Semantic.halts_iff` still
  require that premise explicitly.
- `semanticCovered_of_mixedSites` requires a proof of
  `shared Q e = true -> EdgeContract M Q e`. The Boolean selector alone cannot
  discharge a physical obligation. Exact `ptree` equality and exhaustive
  `allSites` coverage connect the finite evidence to the actual source.
- The semantic proof uses the same deterministic positive-run induction as
  the previous proof. Both simulation directions remain, including the
  target-length decrease in the reverse direction.
- The original `sim_step`, `sim_stop`, `sim_halt` and `halts_iff` signatures
  are retained and exercised by typed clients. In particular, `sim_stop`
  remains independent of `BoxLemmas`.
- Existing executable definitions are unchanged in the source diff. The new
  semantic propositions and wrappers add an interface; they do not replace
  the transition table, `checkEdge`, `start`, `tgtConf` or `Rel`.

## Evidence checked

The candidate source hash agrees with the accepted focused build record and
with the compiled workspace source. The recorded Lean version is 4.32.0.
The typed audit exercises the four legacy APIs, the semantic halting theorem,
and mixed coverage. Its twelve assumption reports contain only the standard
axioms. `Semantic.halts_iff` reports `propext` and `Quot.sound`; adapters using
the old checker also retain `Classical.choice`. This difference does not
remove choice from the complete machine/calibration endpoint.

The focused verification record covers thirteen project modules and one typed
audit, not the full endpoint closure. No current primitive-family theorem has
been installed through a nontrivial selector, so the patch establishes the
interface needed for future certificate savings rather than already removing
the 6,176 existing site outcomes.

## Report review

The draft's positive-simulation theorem, halt-classification premise and
decoder/primitive/return composition are mathematically sound. Its distinction
between external assistant theorems and an internal ZFC/PA formalization is
correct. The quoted source sizes match the reviewed snapshot.

Two precision suggestions were sent to the report author: describe the finite
reachability result as limited payoff in the *tested* nonrelational domains,
and state the K215-specific initial register mapping explicitly. The full
strategic note includes that mapping and all five excluded source outcomes.
