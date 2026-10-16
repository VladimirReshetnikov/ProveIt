# Batch 149 source 02: restoring substitution/shared-schema tableaux

Arrival `be9e617d2`, archive `zfc_substitution_engine.zip`. Untouched source `/tmp/zfc-intake-149-8lt55_fi/02/zfc_substitution_engine`; review/execution copy `/tmp/zfc-batch149-theory-review-fw5hc93s/02`. Pin `47f3a3602946dfe48803a91a910c646e74637ac8`. Full report (all section sources, including theory/correctness/engineering/research/references), README/Makefile/STATUS, and every new core Python module were read. No delivery/repository edits, manifest checks, line-ending work or Lean/Coq builds. Bic owns the engineering suites; this dossier covers mathematics and the new checker/codec/diagnostics.

## Verdict

Continuation of the existing zfc-closure-kernels host. No concrete soundness/completeness, binding or codec error was found. The report supplies a useful new complete reference implementation with **dynamic** parameterized axiom insertion and a shared fixed PSC template. It does not supply a new theory, a verified Python kernel or a compiled small table for that algorithm. The separate268-state artifact retains the complete original logical frontend and is explicitly a compiler control. Its operation-level certificate does not prove binary simulation or the internal ZFC endpoint. The new diagonal counterinterpretation refutes a tempting logical repair, not ordinary PSC or the shared-template checker.

One minor packaging pointer is stale: `code/diagonal_obstruction.py`'s opening docstring locates its proof in nonexistent `theory_support.tex`; the actual proof is `sections/obstruction.tex`. This does not affect mathematics or execution and requires only a host-side locator correction, not alteration of delivered source.

## Mathematical audit

### Theory and internal endpoint

The exact theory is the inherited **ordinary one-domain equality-free subset-seeded PSC schema**, with arbitrary quantified matrices/finite parameter lists, globally subset-bounded fibers as a conditional premise and an unrestricted supporting input. There is no semantic truth oracle, IR addition, logical equality surrogate or restricted list of allowed matrices in the new checker's axiom interface. It is an infinite effective schema, not one finite sentence.

The full hereditary-saturation argument is reproduced accurately: two-sided observational equivalence supplies the raw twin decoder; raw covers and Separation/Union allow exact incoming-profile saturation; the purity cut gives upward hereditary saturation without choosing a family of covers; membership descends to the pure profile quotient. Guarded arbitrary translated matrices and subsequent hull saturation preserve closure/support. This is inherited ordinary mathematics, with the full first-order bridge still beyond the present Lean semantic/control modules. ExtPSC↔ZF0 and Foundation/Choice consistency comparisons are kept distinct. The model argument uses set-coded models from completeness, not an assumed transitive ZFC model.

For the new **specified abstract algorithm**, the soundness/completeness and effective syntax arguments are available in ZFC and compose with that inherited ordinary calibration. No serialized ZFC derivation, theorem about physical CPython, proof-assistant verification of its code or literal binary endpoint is supplied. The report also correctly distinguishes consistency from the extra assumption needed to infer two-sided independence. Intended mathematical meaning is not required; all alternative input/interpreter/boot costs still count.

### New diagonal obstruction

The interpretation has genuine coordinate quantification over two bits, but atom truth is `[i≠j and s(i)=s(j)]`. This is intentionally not a single binary-relation structure. Ordinary Boolean laws, quantified implication, MP/GEN, same-variable specialization, S5 introspection, commutation, full side-conditioned vacuity, alpha conversion and capture-avoiding injective renaming hold. For an off-diagonal atom involving the quantified name once, both signs vary across its coordinate, so each signed-atomic UI has false antecedent. A diagonal atom is constantly false and remains diagonal after simultaneous replacement. Fresh substitution preserves the syntactic equal/different pattern of atom arguments and has the ordinary structural satisfaction induction.

For distinct x,y,z, let A=((R(x,y)↔R(x,z))↔R(y,z)). Equality of two bits makes forall x A true at every assignment. After identifying x with existing y, A becomes ((false↔p)↔p), uniformly false. Hence full colliding UI for this **composite** matrix fails although all the listed signed-atomic/fresh rules hold. The ordinary proof is sound and its finite checks match it. This is a useful strictly stronger warning about logical repairs. It is expressly **not** claimed to validate PSC or C/G, so it cannot be used to prove their consistency/nonhalting. The earlier full finite-sort result supplies the stronger theory-specific rejection; the report accurately reconciles that result and its conditional application to literal tables.

The separate fixed-slot identity-quantifier models (only R01 true, or R(i,0) true for i≥2) correctly validate the literal code+2 PSC wrapper. They do not contradict the full shared-template/common-domain source theory.

### Shared template and closure semantics

`code/lazy_psc.py` generates the fixed hygienic PSC context once. It contains48 tree occurrences (18imp,11forall,7relation,9Bottom,3holes),36 distinct subtrees before pointer costs. The holes have pairs (2,0),(1,0),(0,1). The actual matrix is never input to the fixed-context generator. The declared occurrence equations45+3m versus48+m are correct, including the fact that a one-node matrix is larger in the shared version. These counts exclude term payloads, pointers, environments, maps, proof branches, parser and initialization and are not TM states.

`Closure.expose` enters a source matrix with an **empty matrix bound stack**, retains the root map, and saves precisely the two selected template-environment IDs. Its internal quantifiers then extend only that matrix stack. This corresponds to capture-free insertion with wrapper indices shifted under internal matrix binders; old local matrix indices remain unchanged. `materialize` is only a diagnostic expansion and is not used in acceptance. Two other finite evaluators compare lazy/materialized/direct mathematical PSC semantics independently.

All source terms are parsed for correct free/bound shape, nonnegative non-Boolean payloads and bound index scope. User holes/equality/assumed axiom conclusions are rejected. Slot0/1 values come only from the saved overrides; all other labels use the finite root map with default parameter0. Arbitrarily large syntax labels therefore do not allocate objects or violate freshness. Parameters need not be distinct. Atom closure compares the **evaluated ordered pair of IDs**, so existing variables can actually be identified in composite formulas.

### Dynamic AX and allocation

The checker fixes a nonempty parameter domain by initially allocating p0. AX appends only the exact PSC template for a valid matrix-pool member and a finite map with unique keys≥2 and values below the current counter. Omitted labels denote p0. It can occur after a negative universal introduces a fresh witness. Thus universal parameter instances are not frozen before needed witnesses exist, and no matrix free-label scan/prefix builder is required at runtime.

The allocation invariant covers every active closure's bound stack, saved slots and **hidden map values**. Delta uses the old counter and increments it; gamma checks an existing ID; AX checks every stored value; expose only copies existing values; all branch structures are immutable. Therefore delta freshness holds for the entire active branch, not just visible syntax. Branch splits inherit a counter but may reuse the same fresh ID independently in different branches, which is sound. Every branch still closes; early success does not discard pending siblings.

### Soundness and completeness

The seven instruction contracts in `lazy_psc.check` match signed tableaux:

- negative implication appends positive antecedent and negative consequent;
- positive implication checks both negative-antecedent and positive-consequent branches;
- negative universal allocates a fresh counterexample;
- positive universal may use **any** allocated ID and can be revisited;
- complementary atoms require opposite signs and the same evaluated ordered pair;
- only positive primitive Bottom closes;
- AX is the exact checked schema instance, never an arbitrary premise.

The source/theorem envelopes are exact. The optional closed-theorem interface does not mark demonstrations as refutations. The numerical search calls check with its fixed negative-Bottom root and has no theorem-target field. The CLI rejects null as an explicit theorem file. Pending branch tuples ensure every child is checked.

Soundness follows either by branch satisfaction/materialization or a finite ordinary tableau translation; every axiom map is a finite universal instantiation of an actual closed PSC axiom. Counter freshness is the needed hidden-environment side condition. No injectivity assumption on object assignments is needed.

For completeness, retain all entries and schedule gamma for all eventually allocated IDs, delta for every negative universal, and AX for every pool matrix and finite parameter map when its values become available. If no finite closed tableau exists, the usual finitely branching fair construction has an open saturated branch. Its nonempty domain is the branch's parameter IDs. The signed truth lemma holds over the entire eventual domain because old universals are revisited after new IDs appear. Each matrix has finitely many relevant parameter labels; any assignment of those labels appears in some finite late AX map, so the extracted model satisfies every closed schema instance used by the original refutation. Contradiction establishes a finite accepted tree. This is a valid ordinary completeness argument and does not rest on the finite tests.

### Total natural codec and fair search

`code/certificate_codec.py` was read in full. Formula tags allocate distinct residues with Bottom0 and all recursive children smaller than their parent. Proof tags0/1 are leaves; every recursive tag≥2 makes each unpaired child strictly smaller. In particular proof code0 is finite X(0,0), not a recursive decoder loop. Lists decrease at each positive tail; integer square root makes unpair exact. The whole pairing enumerates every finite matrix pool and instruction tree, with arbitrary map entries and term/name payloads. Scope, allocation, duplicate/reserved map keys and inference applicability are checked afterwards, so total raw decoding does not assert validity. Every accepted finite certificate is represented and every mathematical candidate check terminates. Physical memory/recursion failures and an exhausted finite search limit are not interpreted as refutations.

### Separate engineering control

The source explicitly says the268-state word changes the original theory conjunction layout, while retaining all8 logical/equality rows, oldrho6, both vacuity factors and base4 arithmetic/enumerator framework. Relative conjunction is F∨(A∧B), so the stated commutations/associations are classical tautologies even before F is proved false; the full original calculus transports them. The register certificate compares the **re-emitted revised word** with its compressed version, not the original word. This is a materially correct distinction. Its4533 pairs/both decrement exits do not themselves prove that mathematical rewrite or the binary interpreter/boot. Framework62 plus decision206 is268; no unsupported subtraction of framework costs or new record is claimed. Bic's separate execution audit owns exact artifacts/search claims.

## Reproduced mathematical/Python suites

Exact commands/cwd/Python executable/times and exit0 results are in `/tmp/zfc-batch149-theory-review-fw5hc93s/verification.json`. Python3.13 came from `uv run --no-project python`; scripts used `-B` and only the standard library. All passed on the copy:

1. `code/verify_artifacts.py` (3.508s):12 focused tests;1920 three-way semantic comparisons on24 matrices/domains1–3 (1230true690false);all five numeric families10,000 roundtripseach; boundedprefix10,000 noacceptance. Three accepted **theorem** examples: universalUI5actions/1branch, compositecollision50/16, lateAX103/25 with1AX/3matrix exposures. Search cannot import these targets; changed gamma collision, future IDs, duplicate/reserved/Boolean maps, scope/private holes, wrong signs/references reject.
2. `code/independent_review.py` (9.196s):8568 direct mathematical PSC comparisons over84 matrices,three maps each, all2 one-element/all16 two-element relations and16 sampled three-element relations;504+4032+4032 comparisons. Six logical/parser rejection probes pass. This oracle does not call the materializer or its ordinary evaluator.
3. `code/diagonal_obstruction.py` (.355s):200 fixed-slot identityPSC cases;8192 signedatomicUI;12000freshUI;12000alpha;72000modal;4000permutation assignment cases. Composite colliding UI fails on all8 two-bit assignments as asserted.
4. `code/certificate_codec.py --limit 10000` (.170s): bounded diagnostic completes, no accepted refutation, no consistency inference.

No manifest checker or unbounded proof search was run. The source's root reproduction driver has no manifest step, but it would repeat the core tests and engineering work owned by Bic; individual constituent commands were used instead. No theorem about the unbounded algorithm is inferred just from the passing samples.

## Current repository overlap/gaps

- `Computability/BusyBeaver/Research/ZFC/typed_countermodel.md:1,25–29` already retires reduced C/G for either rho6; lines38–44 preserve missing literal simulation. Source02's contrary treatment of source11's older certification recommendation is the correct current reconciliation, not a new inconsistency among accepted theorems.
- `.../Lean/BusyBeaver/ZFC/RawPSCProfile.lean:22,44,78,96,126,156,164` already supplies Full/twin congruence and the semantic bootstrap. `RawPSCModel.lean:22,44,136,153,175,188,257,265,271` already supplies actual equality-free schema adapters/resources. Source02's broad future-work statements must credit these later additions. `pure_hull_of_model` at292 still assumes actual relation definability and the internal pure bound/invariance at294–295; all-formula H interpretation/quotient calibration remains a meaningful open formal task.
- `PSCSaturation.lean:192,217` gives semantic guarded-hull transfer under explicit resources, not closure under every external relation. `PSCCalibration.lean:166,171,175` is the Ext+PSC control against ZF0, not a complete raw-PSC theorem.
- Source13's complete environment-tableau reference, source16's complete Hilbert checker, and source17's complete ground-clause reference target the same ordinary theory. This source implements an explicitly suggested optimization of the first: fixed shared context plus dynamic parameterized AX. None is already a compiled new machine. Source01 of the same batch offers an independent binder-witness Hilbert alternative.
- `Bottom3Syntax.lean:252,306,314` formally establishes codec freshness and ordinary semantic roundtrips for a different ternary codec. It supplies neither this new formula/proof codec nor an executing decoder/simulation bridge. `RegisterBisimulation.lean` supplies useful generic semantic machinery, but no instantiation is proved for these4533-pair Python certificates.

The most useful next task is to formalize closure lookup/matrix-call satisfaction and hidden-map allocation, then finite signed proof soundness/materialization. The complete dynamic AX/gamma interface is a viable reference contract for state minimization. Passing just the displayed collision example or defeating one old countermodel is insufficient as a calibration proof. A whole compiled search, initializer, numeric/table semantics and internal ZFC bridge are still required; no current goal-completion claim is justified by this intake alone.
