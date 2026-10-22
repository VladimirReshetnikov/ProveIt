# Upstream49: shared implication and import-cut review

The upstream shared implication pair is a better next candidate than our held three-file phase13 prototype. It implements the same semantic sharing, but a genuinely different 58-step derivation absorbs the five additional MP steps used by our exchange/S extension. It preserves the current generic and unrestricted public interfaces and the complete Tarski bridge. This is an ordinary source review with an independent finite syntax diagnostic, not fresh Lean acceptance.

The reviewed range is `437804fcdd5550fec6ece3b6073c616690d4625f` to `49e99c5b7cc6c2e164331961de28bad3904361fd`: four commits and ten changed paths. Drop's separate merge census supplies exact Git/current/input preservation bindings. I read the new generic proof, unrestricted adapter, complete research renderer, derivation and documentation, and the import-cut changes. No renderer, compiler or submitted code was run.

## The shared proof

The first31 private proofs agree with the current core. The changed suffix derives composition, exchange, prefixing and S within the same58 MP derivation; K and Peirce reuse the existing early schemas. The last commit inlines only the two goal lemmas with no dependent lemma: the unrestricted row and S. Composition remains a named private schema because later proofs use it. Thus the final file has56 private MP proofs, two public inlined MP proofs, and the existing one-MP lifting application. There are23 restricted-row uses.

My independent strict free-constructor reader checks every private proof and all six public conclusions, including each side-condition proof. Its only relation rules are a declared hypothesis, reflexivity and insertion into the left/right operand. It accepts no truth element, numerical zero, implication collapse, injectivity, order transitivity or extra inference rule. All checks passed. This diagnostic does not replace Lean elaboration.

`Language`, `rho8`, `Restricted`, `rho8_all`, `composition` and `lift_right` keep their current headers. New exports are `k`, `peirce` and `s`. The unrestricted adapter uses the relation `True`, with trivial reflexivity/growth and the exact rho8 argument order. The old `Lukasiewicz.Implicational`, K, Peirce, composition and S headers are unchanged. Its entire Tarski namespace tail is byte-identical, so explosion still uses the original rho6 and no stronger completeness or consistency statement is asserted.

The upstream pair is18,243bytes/401lines versus42,454/811 for the current checked pair:24,211bytes/410lines fewer. Our held phase13 prototype is18,407/418 across three files, so upstream saves another164bytes/17lines and one module. The two shared-basis implementations are alternatives, not additive savings. An inert import overlay on checked phase12 remains179 endpoint providers and184 with the five prefix providers, with no new module or import cycle.

## The import split

Commit e066 adopts the smaller alternative cut. Its `ZFModelSemantics.models_ZF` has the exact statement/body already checked in current `ZFModels`; both use the original `ZFNative` namespace. Current phase12 additionally separates `WFModelCore`, keeps `InductiveAttempts` explicit, and cuts the L2 producer import to Code254. Replacing these with upstream's broader WFModel wrapper gives back dependencies. Importing both semantic-module versions could duplicate the same declaration. Preserve the checked phase12 split; this upstream cut provides no additional saving.

## Producer and adoption boundary

The supplied renderer is ordinary untrusted source generation. Its new core-only branch uses a goal's explicit MP premise instances when no lemma refers to that goal and exactly one requested public theorem uses it. That is a sound syntactic inlining for the actual six unguarded goals. The existing Lean kernel remains the arbiter. The conditional template is not a general partial-basis interface: requesting K without the other optional basis goals can leave missing template values; this is irrelevant to the exact held six-goal input but argues for retaining the maintained strict fixed-input route.

Current maintained producer `31fdd538…` pins `derivation_core.txt` to `f0a2e60d…`. The new six-goal input is `4141248e…`; replacing it silently would fail the old producer's default check. Keep the historical input available until a reviewed self-contained successor is synchronized. The successor should read raw input as data only, check all56 retained private proofs and six public targets, retain the exact Nat adapter, and emit the held core bytes. No obsolete template needs restoration.

Upstream reports selected `lake build` results, but those claims are not this repository's new actual evidence. The upstream status note's409 combined lines predates the last inlining; the current pair has401. No new K215 endpoint, machine change, unconditional nonhalting result, internal PA proof or Rocq acceptance follows from this review.

Recommendation: retain all checked phase12 production bindings during the merge, import the upstream material as attributed proposal data, then check the upstream shared pair with the synchronized maintained producer and current typed endpoint clients. The earlier three-file prototype remains useful preserved research, not another implementation to add alongside it.
