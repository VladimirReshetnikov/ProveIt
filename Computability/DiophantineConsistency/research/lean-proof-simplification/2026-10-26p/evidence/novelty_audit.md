# Prior-proposal audit for DiophantineConsistency

Implementation/source pin: `7fa06d530df54d4aeb2e18027409df082234c69e`.
Final novelty-refresh pin: `6f46a5e3480a2fa2e45993b8090826f256aeaa56`.

## Final assessment

The final recommendations contain five mechanisms: the scale-parametric Pell ratio estimate, arbitrary-premise backward-reference construction, successor-shifted fork-certificate equivalence, projected support-difference separation, and the deterministic square-pairing witness normal form. Novelty is scoped to this corpus and to each precise mechanism, not to general techniques such as induction, canonical witnesses, or reusable APIs.

**Two initially promising candidates were removed after the final refresh:** congruence up to sign is already explicit in P10/P11, and the affine depth/witness budget is already explicit in P11. Their code and recommendations should not appear among the final new proposals. Stronger local validation does not make a repeated idea new.

## Corpus and interpretation

Seven ZIP archives in docs/incoming at source_commit, the directly linked retired DiophantineConsistency simplification manuscript, and three additional ZIPs present at refresh_commit; all eleven relevant manuscripts and substantive supplements reviewed. The intake README and refreshed adoption record were inspected. Older K215 intake dossiers linked from the README were not exhaustively followed.

The ten archive containers were safely extracted as data; their 2,193 members were inventoried with SHA-256 hashes. The eleven manuscripts comprise 18 primary LaTeX source files, totaling 498,645 characters. Primary manuscripts, substantive supporting notes, and relevant prototypes were inspected. Bundled repository snapshots and bare filename inventories are source evidence, not automatically proposals. This is a conceptual nonduplication review of the requested intake lineage, not a claim of global novelty.

At the original pin the README-referenced adoption file was absent from its old destination. At the refresh pin it exists at `Computability/DiophantineConsistency/research/lean-proof-simplification/ADOPTION.md`; its contents and the refreshed intake listing are preserved in `latest_intake_review.json`. The adopted changes include old list/Option APIs, PR congruence, and assignment mapping. None of the five retained mechanisms is listed as adopted. The parent task separately checks latest-source compatibility.

## Source key

- **P1**: archive `Lean_Proof_Simplification_2026-10-26.zip`, member `Lean_Proof_Simplification/report/report.tex`.
- **P2**: archive `ProveIt_Lean_Proof_Simplification_2026-10-26.zip`, member `LeanReview/report/sections/`.
- **P3**: archive `diophantine-lean-simplification-2026-10-26(1).zip`, member `diophantine-lean-simplification/report.tex`.
- **P4**: archive `diophantine-lean-simplification-2026-10-26.zip`, member `diophantine-lean-simplification-2026-10-26/report.tex`.
- **P5**: archive `lean-proof-simplification-2026-10-26 (2).zip`, member `lean-proof-simplification-2026-10-26/report.tex`.
- **P6**: archive `lean-proof-simplification-2026-10-26.zip`, member `lean-proof-simplification-2026-10-26/report.tex`.
- **P7**: archive `lean-proof-simplification-review-2026-10-26.zip`, member `lean-proof-simplification-review/lean-proof-simplification-review.tex`.
- **P8**: repository file `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`.
- **P9**: archive `diophantine-lean-additional-simplifications-2026-10-26.zip`, member `diophantine-lean-additional-simplifications-2026-10-26/report.tex`.
- **P10**: archive `diophantine-lean-new-directions-2026-10-26.zip`, member `new-lean-simplification-2026-10-26/report.tex`.
- **P11**: archive `diophantine-lean-new-ideas-2026-10-26.zip`, member `diophantine-lean-new-ideas-2026-10-26/report.tex`.

## Exclude these already-proposed mechanisms

Locations are line numbers within the named archive member, not the production Lean file. P2 locations name the section file. Families are conceptual: a renamed helper, a new code style, a second client, or a stronger validation receipt alone does not create a new idea.

| ID | Prior mechanism | Evidence | Consequence for this iteration |
|---|---|---|---|
| `existing_library_lookup` | Core List lookup/member and Option map injectivity | P1:162-182; P7:222-254; P8:132-142 | Replacing private list inductions or encoded-list injectivity by these APIs is already proposed. |
| `recursor_congruence` | Transport pointwise equalities directly through Nat.rec | P8:114-130 | Includes PRCode, ScalarPRCode and ScalarPROptimizer; do not present a generic recursor congruence helper as fresh. |
| `assignment_naturality` | natAssignment composed with Sum.map; finite witness-block splitting | P3:136-174; P7:371-427; P8:144-160 | Includes reindex/conjunction/disjunction, nested sums and existsBlock extensions, and moving projections lower. |
| `sum_squares` | Shared finite residual-sum evaluation and zero iff all residuals zero | P3:370-380; P7:428-505; P8:162-188 | Also generic sum cost, polynomial degree bound, and signed/natural compiler comparison. |
| `gate_semantics` | Share generic gate soundness/completeness across semirings and wire codecs | P4:443-468; P5:541-576 | Signed two-coordinate and nonnegative one-coordinate realizers retain separate hypotheses and costs. |
| `topological_invariant` | One strong induction/invariant for topological DAG registers | P3:332-341; P7:707-728; P8:240-254 | Includes uniqueness, degree, nonnegativity and some append/topology bookkeeping. |
| `register_append` | Shared append proofs for register topology/evaluation | P8:272-276 | Do not relabel the same old-index/new-index split as a novel builder API. |
| `power_step_certificate` | Indexed run_node_equation facade and existing exponent-label PowerStep checker | P2:04_circuits.tex:11-166; P3:295-350; P8:190-238 | Both broad certificates and preserving/generating old named wrappers are prior. |
| `semantic_blocks` | DAG semantic block certificates and dependent safe-node/checked-circuit views | P2:04_circuits.tex:167-242; P1:287-303 | Must bind to exact existing DAG; typed circuit views themselves are not a new proposal. |
| `shared_tail` | Identical Split/Gap free-carrier polynomial and 99-node circuit suffix | P1:234-255; P6:468-540 | Includes shared map laws, 22-let tail correctness, register instantiation and generator-template reuse. |
| `translations` | Generic circuit simulation with prefix/input/ref map and commutative NodeRel swaps | P3:352-369; P6:711-738; P8:256-270 | Shift x→x-1 is not a ring homomorphism; both reports state this explicitly. |
| `degree_profiles` | Shared ShortSystem degree prefix and Split/Gap degree profile | P2:03_architecture.tex:172-213; P2:04_circuits.tex:188-210 | Also move syntaxDegree down import graph; retain cancellation normal forms and sharp bounds. |
| `coefficient_envelope_tactic` | Factor 22 coefficient envelope proofs with structural abs_ite_le and one arithmetic context | P3:435-441; P6:330-383; P7:139-198 | Prior fully compiled candidate has an observed 4.7x CPU increase; terse code is not an unqualified speed win. |
| `coefficient_majorants` | Eight-monomial nonnegative basis and finite componentwise majorant certificate | P6:407-426; P7:199-219 | Explicit triangle inequality and small integer coefficient vectors already proposed. |
| `coefficient_naturality` | One finite-row homomorphism dispatcher or computable syntax interpreter | P2:03_architecture.tex:214-248; P6:384-406 | Includes eliminating duplicated hleft/hright formulas and binding syntax to authoritative rows. |
| `row_reflection` | Sparse quadratic row normalizer; rewrite-before-degree block certificates | P3:382-394; P6:754-773 | Broad expression reflection/normal forms are prior; a different quotient relation needs a concrete mathematical distinction. |
| `row_operations` | Elementary row-addition zero-set preservation and surjective row reindexing | P6:774-808 | Full matrix approach is mentioned as later extension for arbitrary invertible combinations. |
| `scanner_iteration` | Fixed states, successor iteration, invariant preservation and encoded-list simulation | P1:186-212; P3:256-294; P6:541-600; P8:278-310 | Raw arbitrary-input soundness versus encoded completeness explicitly distinguished. |
| `history_folds` | Heterogeneous Line/Judgment history fold, run_append, Produces.append/step | P1:232; P4:284-327; P6:601-613; P7:524-555; P6:notes/syntax.txt:76-88 | Reversed history order and certified composition for fragment2/fragment3 are explicit. No arbitrary-premise list compiler constructing suffix-length parent indices was found. |
| `pr_builder` | Realized iterateFrom/iterateProgram, shared direct/native graph builder | P1:356-365; P4:362-379; P6:614-623 | Preserving actual program data and witness/node costs is part of the prior proposal. |
| `boolean_dispatch` | Exact numeric 0/1 checker value from Booleanity+acceptance; threshold tag dispatcher | P1:214-232; P4:380-396; P8:296-310 | A new Boolean wrapper using the same two premises is a repeat. |
| `parse_codec` | Parse-then-check composition and left-inverse decoder-to-injectivity helper | P3:445-453; P7:310-339 | Includes successful Option.bind_eq_some_iff destructuring; broad codec cleanup overlaps. |
| `decoder_fusion` | Fuse successful decoder depth/quote correctness into one induction | P7:340-369; P9:182-220; P10:123-167 | Joint soundness plus exact arbitrary-code/fuel graph theorem also appears in refreshed packets; not a new recommendation. |
| `half_radix` | Scaled div/mod identity removes 4×4 digit enumeration | P3:176-198; P5:310-374; P8:319-329 | Exact identity s*a%(2*s)+s*b/(2*s)=s*(a%2)+b/2 is prior. |
| `modulus_interfaces` | Common addition/subtraction/source residue interface and weakening 2048 to16 | P2:02_local.tex:176-209; P3:229-239,398-412; P8:313-318 | Preserving whole-cell motion while taking local residue is explicit. |
| `divmod_carry` | One quotient/remainder certificate and normalized carry decomposition | P1:174-182,320-331; P3:209-227; P4:644-677; P8:343-353 | Includes removing redundant recurrence fields, exact quotient/modulo/reset consequences. |
| `word_origin` | Generic origin subtraction correction for packed words | P3:414-425 | Guard q≤a0 for truncated natural subtraction is explicit. |
| `sparse_placement` | Injective sparse placement API with image/off-image lookup, bounds and population | P3:427-433 | Bounded positions represented by Fin n and ZMod.finEquiv are explicitly suggested. |
| `fiber_pushforward` | One finite-fiber weighted sum identity for mass, convolution and word | P5:415-445 | Allows collisions and noncommutative multiplication; no injectivity assumption. |
| `finite_word_interface` | Boundary between ZMod, Fin, List.ofFn and finite sums | P7:619-634 | Also geometry record for modulus/range/wrapped index consequences at 635-647. |
| `window_views` | Shared source/window extraction, coherent witness N, derived Facts views | P1:305-332; P2:03_architecture.tex:99-171; P6:869-912 | Includes import split CurrentCarrierBase2011 below completeness and named conjunction accessors. |
| `conditional_padding` | Make padding witness existential only in middle-phase branch | P8:330-341 | Removes dummy zero witness; changing quantifier order is already proposed. |
| `packed_fields` | Finite field descriptors and shared four copied-field bounds | P1:338-350; P4:712-725 | Packed direction order and ColorsBounded order differ and must stay explicit. |
| `chunk_assembly` | Euclidean block+tail dispatch and balanced assembly of finite sum certificates | P1:334-337; P4:678-711 | Finite leaves retain kernel checks; not a new certificate framework. |
| `pell_source_decode` | Named q=1+Jβ,L=q²−1,N=q³,X=qw facts from literal source rows | P4:617-641 | Targets NativePellBootstrap and NativePellPower; not the same as a new sign-orbit quotient API. |
| `pell_cast_cleanup` | Use omega directly in NativePellStepDown.eq_of_residues; whole disjunction exact_mod_cast | P7:289-300; P1:156-160 | Bound/cast cleanup alone is prior; sign transitivity/negation is separately excluded after the refreshed packets. |
| `guarded_zero_transport` | Lift pointwise zero-set equivalence through guards/existence; nine-coordinate packing | P1:257-285; P2:03_architecture.tex:11-67; P3:240-254 | Many-to-one witnesses need not be equivalences; positive/natural slot7 asymmetry explicit. |
| `object_transport` | Completeness+sealing wrapper, model→axioms bridge, definable internal induction | P3:463-477; P6:809-868; P7:556-602; P8:355-371 | Actual formula/satisfaction spec and model quantification retained; external predicate induction invalid. |
| `object_indices` | Closed-sentence arity polymorphism and finite-index conjunction plumbing | P3:455-461; P6:829-850; P4:768-781 | Fin.forall_fin_add and Fin.forall_fin_two already suggested. |
| `small_arithmetic` | Standard sum≤1, finite set intersection, predecessor exponent, symbolic huge powers | P2:02_local.tex:105-175; P3:199-207; P7:255-309; P11:143-199 | Also exact Nat power lemma and finite-switch complement normalization. Exact finite-support sum_le_one_cases migration is now explicitly proposed. |
| `audit_policy` | Consolidate pure audit wrappers, explicit checks closure, axiom policy gates and profiling | P2:05_validation.tex:39-107; P1:367-407; P8:373-393 | Validation methods are required practice, not fresh proof ideas. |
| `finite_cycle_rank` | Future finite-state controller certificates with ranking/SCC for cycle exclusion | P1:354 | Broad direction explicitly prior. Concrete Lyapunov construction may be new work but must acknowledge this precedent. |
| `rational_root_preserving_descent` | Preserve chosen rational roots when descending to integers via denominator-one lemma | P9:121-157 | Retains signs and linear relations rather than choosing replacement square roots; shared finalizer theorem is also prior. |
| `product_unit_decomposition` | Decompose all integer factors of a product equal to one using IsUnit.mul_iff | P9:159-180 | One tuple of ±1 alternatives replaces repeated product rearrangements in ShortSystem. |
| `finite_invariant_predecessor` | Restrict a finite injection to a forward-invariant subset to obtain an invariant predecessor | P9:222-248 | Exact NativeFieldCycles2011 offset-19 application is already supplied. |
| `univariate_support_envelope` | Bound polynomial natDegree before proving coefficient vanishing | P9:250-281 | SelectiveCarry support envelope avoids nested coefficient expansions; distinct from projected group difference sets. |
| `rotation_point_mass` | Deduce cyclic rotation from convolution with Pi.single | P9:283-307 | Direct specialization of existing word_convolution is already a checked patch. |
| `primrec_fun_prop` | Register extensional Primrec composition rules for fun_prop | P9:309-346 | Local registrations and constructor adapters are already provided; executable PR-code construction remains separate. |
| `canonical_carry_uniqueness` | Finite-maximum principle gives carry uniqueness after digits or a full packed word are fixed | P9:348-394 | Canonical carry interface and fixed-length digit injectivity are prior; modular equality alone is insufficient. |
| `signed_modular_orbit` | Congruence up to sign, transitivity, negation and natAbs transport | P10:169-215; P11:497-561 | Exact same mechanism and NativePellStepDown/SignedPellResidue clients; exclude entirely from new recommendations. |
| `internal_constructor_unique_exists` | Tagged semantic constructor views plus one internal unique-existence induction | P10:217-274 | ObjectCodeBound totality/functionality fusion is prior; retains definable induction on nonstandard internal codes. |
| `internal_graph_preservation_fusion` | Invariant preservation and fusion for internal recursive graphs | P10:276-345 | ThetaG clients use totality, functionality and definable induction; generic graph preservation is prior. |
| `depth_maxplus_certificates` | Small baseline/excess certificates for representation depth | P10:347-404; P11:489-495,634-637 | BoundedForallDepth factorial/product plans and future max-plus automation are already proposed. |
| `explicit_cyclic_carries` | Closed least/greatest cyclic carry formulas and precise two-solution classification | P10:406-506 | Exact-witness/canonical-carry construction is prior, though production Lean formalization was left open. |
| `pell_parity_reuse` | Reuse SignedPellResidue.odd_index_of_base_dvd in NativePellStepDown | P11:201-251 | Includes deleting unused hs0 positivity proof; do not treat this cleanup as new. |
| `pairing_equiv_projections` | Derive inverse-coordinate graphs from a product equivalence | P11:253-349 | Targets include QuadraticNatPairing inverse graphs; does not determine selector/slack/max witnesses. |
| `euclidean_certificate_uniqueness` | Share positive-denominator Euclidean certificate across register/quadratic backends and prove witness uniqueness | P11:351-413 | Exact shared theorem plus q/r/slack uniqueness is prior; retain positive denominator guard. |
| `affine_depth_witness_budget` | One arithmetic budget pays composition depth overhead with newly introduced witnesses | P11:415-495 | Exact GraphSizeBounds Thin clients, coefficient six, and zero-arity distinction are already proposed; exclude entirely. |

## Retained mechanisms and precise novelty boundaries

### Scale-parametric Pell ratio estimate

No manuscript discusses `PellRatio90.upper_estimate'` or `NativeHalfBinomial.upper_estimate_scaled` as a scale-parametric estimate. P10/P11 concern signed residues and parity, and P4 packages literal source-register equations. The new theorem varies a real factor in the analytic growth estimate and specializes it at one and two. It is not the already proposed half-radix division/remainder identity. The checked theorem is Pell-specific and over the reals; do not describe it as a fully generic ordered-field API.

### Arbitrary-premise fragment construction

P4:284–327 and P6:601–613, especially `notes/syntax.txt`:76–88, already propose shared `run_append`, invariant folds, `Produces.append`, `Produces.step`, and a certified fragment-composition interface for `fragment2`/`fragment3`. Reversed histories and backward-reference sensitivity are explicit. The retained additional result assembles fragments for an arbitrary list of premises while synthesizing parent indices from suffix-history lengths, then derives all four old arity wrappers. No such arbitrary-list compiler or invariant was found. Claim this narrow extension; do not advertise shared fragment infrastructure itself as fresh.

### Successor-shifted fork certificate

No manuscript gives `ForkCertificate (out+1) ...` as an unconditional equivalence to the ordinary square-pairing certificate, followed by one impossible-zero case. The final checked production patch adds `forkCertificate_succ` and handles zero locally inside `forkCertificate_iff`. This is a concrete arithmetic boundary simplification, distinct from generic positive/natural witness packaging.

### Projected support-difference separation

No manuscript proves that a projected displacement outside `S-S` forces one of two supported digits to vanish. P3's sparse placement, P5's finite fibers, P9's univariate degree support envelope, and P11's one-hot support classification are different statements. The numeric `no_difference_606` obstruction already exists in the baseline; novelty is the reusable projected-support elimination rule, not the arithmetic obstruction itself. Keep ambient translation and projection distinct and work in additive commutative groups.

### Canonical square-pairing witnesses

P11:253–349 already simplifies inverse graphs by projecting a product equivalence, including clients in `QuadraticNatPairing`. P11:351–413 also shares positive-denominator Euclidean certificates and determines their quotient/remainder/slack. Those are important nearby precedents. The retained result specifically proves the quadratic square-pairing rows equivalent to `z=Nat.pair a b`, selector `if a<b then 0 else 1`, the corresponding slack, and `m=max a b`. It determines the existing three auxiliary witnesses and is stronger than output-only soundness or existential elimination. Generic claims about introducing canonical witnesses would be too broad; keep the claim on this exact normal form.

## Removed after the refresh

- **Signed modular congruence.** P10:169–215 and P11:497–561 state the exact relation `a ≡ b (mod m) ∨ a ≡ -b (mod m)`, transitivity, negation and absolute-value transport, and the same Pell clients. Excluded.
- **Affine depth/witness budget.** P11:415–495 gives the exact `Thin` invariant, aggregate parent/child witness sum, composition-depth rule, three production clients, and the direct-versus-indirect zero-arity distinction. Excluded. P10:347–404 separately proposes max-plus depth certificates.
- **Dead local positive-rank cleanup.** P11:201–251 explicitly removes `hs0` while reusing the existing odd-index theorem. Excluded as a new idea.

## Other candidate limits

Broad partial-codec round trips, decoder fusion, minimum-norm saturation, finite-cycle ranking/SCC suggestions, generic graph/circuit cost frameworks, and shared lookup/fold infrastructure were already excluded. P9/P10 reinforce decoder fusion and add exact decoder-graph characterizations. P9 supplies a concrete finite-invariant predecessor argument for offset-19 cycle exclusion. These are not reserve candidates for a report that promises to avoid repeated ideas.

`module_prior_mentions.json` is an initial lexical steering aid, not the final novelty verdict. Absence of a filename does not prove absence of a family-level proposal. The expanded `novelty_matrix.json` and the precise qualifications above supersede initial eight-manuscript assessments.
