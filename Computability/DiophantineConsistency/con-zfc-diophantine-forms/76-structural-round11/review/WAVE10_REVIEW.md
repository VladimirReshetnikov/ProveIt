# Wave-ten comparison and round-eleven research priorities

## Pinned scope

Reviewed main commit **2605669a532342f153b13eb6b4a0af4b54f5fa37**, dated 2026-10-24 00:56:40 UTC. This is a snapshot, not a claim about later commits. The eight complete packages 68–75 arrived at **9513bd88cefb762dc07e1872be3078d14aca63fe**, were placed at **d79b41884dbb0a2ad292ca6afc4999aca4d80dc8**, and were reconciled in the README at **cf4a5218a5a4e4358d3f5314151b6b05d4aa384e**. The active mathematical/formal review is **1affa014c2e674e6ccb01fc9d49ff965b6613e15**.

Sources: pinned `UPSTREAM_README.md`, five active status/review files in `formal/`, `RECENT_COMMITS.json`, 45 selected literal proof/data files in `packages/`, and all eight complete arrival archives in `archives/`/`arrival/`. `ARCHIVE_PINS.json` records Git blob authentication, SHA-256, sizes and extraction roots. Every ZIP passes CRC, duplicate-name and path-traversal checks. No upstream program was run. The independent local `check_literal_counts.py` parses only JSON and confirms topology, all-gate liveness, operation counts and variable/residual arities for 17 literal files. Its degree fields repeat the source claims and are explicitly not new degree proofs.

## Current frontier relevant to the requested iteration

Domain and metrics must not be conflated. Counts charge binary addition/subtraction/multiplication, including scalar multiplication and squaring, with fixed integer leaves free. Positive coordinates mean strictly positive integers.

| Domain | Variables | Degree | Operations | Source |
|---|---:|---:|---:|---|
| Positive | 9 | 1,845,940 | 443 | Active compact54-sharp rebinding of source66; delivered source66 is444 |
| Positive | 9 | 1,379,730 | 478 |71, shared taps + order-seven majorant + joint-power rewrite |
| Integers |10|1,576,864|481|68, our prior free-Lucas construction |
| Positive |11|325|113|70, three-root transfer |
| Positive |12|82|102|69, rational Pell descent |
| Positive |12|110|100|74, centered product |
| Positive |12|164|99|74, centered sum of squares |
| Positive |12|258|89|57, surviving older cost tradeoff |
| Positive |13|28|98|72, positive congruence coordinates |
| Positive |13|30|92|73, adaptive carrier |
| Positive |13|114|83|62, surviving older cost tradeoff |
| Positive |14|24|101|72, retained product coordinate |
| Positive |14|26|92|65 |
| Positive |14|30|83|64 |
| Positive |14|52|79|55/59 |
| Integers |38|4|not optimized|69 and71, distinct cone guards |
| Integers |32|6|not optimized|69 and71 |
| Integers |27|8|not optimized|69 and71 |
| Integers |26|16|not optimized|68 |

The smallest complete native tuple still uses radix 2^429959 (54). Source68 uses old31; source69/71's extra cone scales enlarge fixed coefficient storage. Source73 binds a sextic to whole compact44, not compact54. Never replace individual coefficient ports across these sources without a complete calibration proof. MF ports are already shifted once.

## What each new package contributes

1. **68 Joint positivity/free Lucas.** Our preceding round: a fixed residue coordinate C=6c−1 replaces a high-degree index congruence; a stronger unsigned-index lemma and mod3 orientation recover the correct index. Also nearest-square joint positivity, local 17-witness proof rules and 23-witness affine proof accumulator. The global proof compiler is not instantiated.
2. **69 Weighted cones/rational Pell.** Canonical native leading-digit bounds permit a fixed weighted cone to enforce two common-sign constraints with one ternary positivity group. This yields38/32/27 integer forms. Separately, rational Pell descent removes denominator guards from the positive12 merger, reaching82/102.
3. **70 Residue orientation/root transfer.** A mod3 affine substitution X=3X3−1 removes a separate square-orientation coordinate. Three-root transfer improves positive11 to325/113. Its direct and residue-oriented integer quartics are two different forms.
4. **71 Calibrated determinant guards.** The cone is U V−(q−U−V)^2 with U=2^1113 F and V=2^666104 C. Universal signed soundness restores the old two sign guards; completeness requires canonical native leading-digit estimates, not a pointwise map from every old zero. Source69 uses different weights and a different polynomial. Separately,71 composes65's source with63's majorant and62's joint powers for the new9-positive degree record.
5. **72 Congruence carriers.** Positive coordinates representing exact residues yield13 variables/degree28 and14/degree24. Six derived constants are counted as fixed leaves; computing them costs seven extra gates. Its34-integer sextic removes different rows from the other siblings.
6. **73 Reanchoring.** Changes which source common-sign products receive ternary positivity guards, enabling different eliminations. Its13-positive degree30 polynomial equals74's but evaluates with one fewer operation. Also supplies a complete compact44 coefficient rebinding of its34-integer sextic.
7. **74 Centered gaps.** Balanced norm and adaptive modulus give12-positive110/100 or164/99. These are lower-cost alternatives to69, not degree improvements. Its13-positive polynomial coincides with73's.
8. **75 Signed bootstrap.** Removes a genuine scale coordinate before monic projection; yields another34-integer sextic. Its inert-prime CRT closure and fixed-input machine boundary are proved interfaces, not completed global ordinary consistency polynomials.

## Immediate synthesis opportunities, with prior disclosure

The intake README already explicitly proposes:
-70's affine residue orientation with69/71's cone guard, suggesting a37-integer quartic;
-68's joint positivity applied to the remaining guards in69/71's27-variable octic; one intake dossier constructed a25-variable degree12 polynomial, without proving its correctness;
-72's elimination with73's reanchoring.

Consequently these combinations must not be presented as previously unmentioned ideas. A new contribution can prove them, complete coefficient binding, find additional eliminations, or establish an actually different mechanism. The broader weighted-cone idea was independently used by68/69/71. A nearest-square or determinant lemma alone is not a historical novelty claim.

More structurally distinct prospects:
- Replace the affine pairwise-coprime proof accumulator with a bounded-height polynomial identity certificate, eliminating the common-multiple block. No wave10 source inspected here completes that idea.
- Reduce the free-Lucas finalizer's square-separation/rank certificate rather than merely alter its coefficient packing.
- Combine rational Pell descent with root transfer or a differently oriented congruence coordinate. Must retain divisibility/saturation and exceptional-index arguments.

## Active formal progress and actual limits

At the pin, the repository has a completed supplied numeric ZFC-refutation checker with83,281 raw and76,313 optimized primitive-recursive program-tree nodes. These are not counts of a flattened Diophantine equation. The literal compiler to quartics has correctness proved over the internal natural numbers of arbitrary ZFC models, with an actual object-language derivation of the source/compiled no-zero equivalence. The actual max-square pairing, predecessor and projection graphs have further internal totality/functionality results.

This does not yet establish the final internal consistency biconditional. Internal syntax/proof-checker transport remains open. On the native side, authentic high-mask binding, phase synchronization and global semantic calibration remain open. External Lean equivalences, finite coefficient checks, source arithmetic and an internal generic quartic compiler must not be conflated with that endpoint.

The three requested generic APIs are retained in `formal/lean/`: BoundedForallRepresentation, QuarticCompiler and RemainderRepresentation, all at the pin. They are source references, not newly compiled here.

## Packaging cautions for the next deliverable

Use complete arrival archives as provenance: placement omits duplicate payloads and ignored manifests, so drivers need not run from the placed directory. Include an explicit release manifest, generated-file whitelist and clear authored/reused-material notices. Avoid references to internal search scripts or prototypes not shipped. Distinguish local witness counts from global counts. A finite reconstruction and independent replay are evidence of transcription and arithmetic checks, not replacements for the unbounded equivalence proofs.

## Sources

- https://github.com/VladimirReshetnikov/ProveIt/tree/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/con-zfc-diophantine-forms
- https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/PROPOSAL_REVIEW_WAVE10.md
- https://github.com/VladimirReshetnikov/ProveIt/commit/2605669a532342f153b13eb6b4a0af4b54f5fa37

This review is an independent read-only comparison, not a new mathematical certificate for every inherited package.
