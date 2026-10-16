# Batch 146 source 01: independent countermodel and compiler-scope review

Reviewed 2026-10-16 in `/tmp/zfc-review146-7l67s9p4/01`, copied from the untouched intake extraction. No original intake file or repository file was changed. No Lean/Coq build, network access, broad source-manifest check, or release checksum audit was performed.

**Verdict:** no mathematical or source-fidelity flaw found in the finite-sort obstruction. It validates the entire specified raw equality-free numerical calculus, including the gated C/G bundle, both quantifier rows, code-zero alias, all numerical parameters, and the abstract enumerator's actual stack operations. It transfers to the source10 conjunction250 and source11 original-rho6/rho8-permuted248 programs at the calculus and abstract-enumerator levels. It does not establish nonhalting of any literal compiled machine. The conditional literal consequence and incompleteness qualification in the paper are necessary and correct.

## Exact formula and source correspondence

The report pins ProveIt `83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373`, with the later PSC supplement separately pinned to `e7c4cadf9b180e4b1801755b09777a7572412360`. These are different experiments, despite both having a 252-state recipe.

The independent scratch program `source01-independent-checks.py` directly compared the report's eight functional compiler inputs with immutable local Git blobs at 83dec60 and with the present repository files. All were byte-identical: the three reconstruction scripts, TMBuilder/tm/tmdb, Dag254.v and spec.py. This was targeted provenance comparison, not execution of the broad authored/vendor manifest. The published spec digest is `7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9`.

That program loaded the current `published_spec()` purely symbolic formula definitions and converted them independently into the report model's AST. C and G agreed exactly in 250 comparisons over all triples of labels 0..4, including every label collision. This checks full constructor trees and scopes, not just printed formulas or names. Relevant current sources are `theory_backend_experiment.py:172`, published `ZF/m254/tools/logic/spec.py:49`, and the report's `code/equality_free_countermodel.py:54`.

In particular:

- The outer existential c in G binds the hull coordinate; the matrix occupying formula position c is the *numeric formula code* c. In coverage, the original b value supplies the domain guard before the inner output binder b shadows it. The second existential b in the range witness shadows that output binder only within its own scope. The support clause has no domain restriction.
- In C's power subformula, the inner universal c shadows the chosen existential c only within the subset antecedent. It does not bind the R(b,c) consequent. Treating those two occurrences as the same bound occurrence would invalidate this review; the actual AST has the scopes used by the proof.
- The compiler gate is exactly c unequal to a and b. It permits a=b. Those collisions must be proved, and the report proves them.

## Mathematical audit

For positive code n, both unpaired components of floor(n/3) are smaller than n. Strong recursion therefore supplies a total interpretation of every natural code; no restriction to finite source formulas is being smuggled in. Including bound labels as well as free labels gives the deliberately loose support bound L(n) subset {0,...,n-1}. Its locality consequence is sufficient: matrix code c is independent of coordinates c and above. Code0 is closed truth. The only implication collision I(0,0)=0 is compatible with truth implies truth; relation and universal constructors have no such exception.

The domain recursion d0=2 and d(i+1)=d(i)+2^d(i) gives nonempty finite sorts. Di contains empty object0 and universal object1 for incoming membership from every different sort. When i<j, the values d(i)+binary-mask represent all subsets of Di inside Dj; they are at least2 and cannot collide with universal object1. E(i,i) is uniformly false, so the distinguished formula F=R(0,0) remains false under every binder update, including label0. Derived conjunction and existential therefore have ordinary Boolean and existential meanings in this interpretation.

The retained Lukasiewicz row is a classical propositional tautology. K and quantifier commutation hold for coordinate quantification, including equal binder labels. Both original `(exists i forall i p) -> p` and dual `p -> forall i exists i p` hold by repeated-label shadowing and nonempty domains. Atomic vacuity holds at the actual gate. MP and generalization preserve global typed validity. The interpretation deliberately supplies no cross-sort substitution or variable-renaming rule; none is present among the raw compiler's rules.

C is valid in all permitted cases. For distinct a,b,c choose outer b=1 and power witness c=1: the relevant consequent and root atoms are off-diagonal incoming membership into a universal object, independently of label order. For a=b the universal a binder shadows outer b, making the guard diagonal and false; outer b=1 still satisfies the off-diagonal root atom. When c=a or c=b, the emitted current formula is truth0 rather than C/G/V.

G's three cases exhaust the gate:

1. If a=b choose hull value0. Coverage has a false diagonal guard; support has no incoming members.
2. If a differs from b and b<c, form the subset of Db consisting of outputs y with some source x satisfying both the *starting-domain* guard E(a,b)(x,B) and the matrix. The exact-subset representative belongs to Dc. Updating c preserves the matrix. The same y witnesses coverage, and the source x witnesses support; support asks less than this construction provides.
3. If a differs from b and b>c, numeric locality makes the matrix independent of b and c. If any guarded x satisfies it, choose hull1; that same x witnesses support for every output and output0 witnesses each coverage requirement. If none does, choose hull0 and both clauses are vacuous.

The b=c case is excluded. At c=0 the matrix is closed truth and only the third-ordering case or a=b is possible; at c=1 the matrix R00 is uniformly false. Thus neither the zero alias nor the low-code cases create an uncovered collection instance. These are ordinary mathematical proofs of all instances; the finite Python cases are transcription regressions only.

A useful check of the failure is `forall v0 R(0,1) -> R(2,1)` with coordinate1=5 and coordinate2=0. Both D0 elements belong to the encoded full-D0 object5, but E(2,1)(0,5) is false. Hence ordinary first-order instantiation fails even with the entire C/G/V bundle. The original equality-existence/congruence machinery is outside this model. The original full equality253/254 benchmark is not invalidated.

## Abstract operational invariant and literal boundary

Published `spec.py:73` distinguishes current tw, cache h, stack ws, and additive counter d. Its exact-arithmetic mathematical specification preserves global validity of tw, h and every Cantor-stack entry:

- successful MP recognizes cached `Imp(tw,d)` and uses valid tw and valid cache to obtain valid d; it pushes truth0; failed MP writes truth0; either branch clears h;
- DROP pushes old tw and installs valid h as tw;
- NIP can halt only on *incoming* h=1; otherwise it pops a valid entry; the zero tail is an endless stream of valid truth0 entries;
- AX pushes old tw, generalization of the *old* cache before the new b read, and valid logical rows; the new current is a valid gated bundle or truth0; it clears d and h.

The candidate-list and additive counters only select natural-number instances already covered. Row ordering does not change validity. Starting zero registers satisfy the invariant. Since code1 is false, the abstract NIP halt test is impossible. ZFC can construct the finite domain sequence, support tables, finite truth tables, and this induction without assuming Con(ZFC). This claim concerns the exact-arithmetic enumerator: the Python diagnostic's bounded/fingerprinted `bignum` execution is not an exact unbounded interpreter proof.

The paper correctly stops short of literal raw252 nonhalting. A ZFC proof that literal halting implies abstract-enumerator halting would yield literal nonhalting in ZFC. Under Con(ZFC), ZFC could then not also prove that nonhalting equivalent to its ordinary consistency statement. The desired PA equivalence is stronger still, since PA proofs can be interpreted in ZFC. This conditional argument must not be shortened to an unconditional theorem about the frozen252/250/248 transition tables.

## Transfer to later retained machine experiments

**Source10 conjunction250: applies.** Its generator keeps the same gated C/G/V, uses the dual rho6, and recursively swaps derived conjunction operands without moving binders, atoms, parameter reads or gates. The independent check extracted the actual `variants()` functions and verified all eight C and four G variants have identical constructor trees after commutative-And normalization. With F uniformly false these swaps and the outer C/G/V reassociation preserve truth at every assignment, including beneath binders. Logical-row reordering is harmless to the validity invariant. This is a statement about the intended numeric program; the existing finite table/auditor facts alone do not supply its TM simulation.

**Source11 original-rho6/rho8-permuted248: applies.** `11-grammar-code-generate_schema_candidates.py:84` permutes only the four schematic parameters in the propositional Lukasiewicz row, with an explicitly checked inverse. It emits C/G/V unchanged, bundle V and (C and G), and rows rho8/rho2/rho4/original-rho6. The independent check confirmed the exact inverse syntax and all16 Boolean values of the permuted rho8. Pointwise validity needs no argument that the coupled numeric parameters enumerate all substitutions. The model also validates original rho6. Re-Pair changes macro representation with its own expansion/register certificates, not the emitted logical axioms; this review makes no extra compiler correctness claim.

**PSC supplement: applies to the inspected abstract rows.** Fresh k=c+2 is distinct from designated0/1 and absent from the matrix. The global range of the matrix over D0 x D1 has a representative in Dk. That range proves the PSC conclusion for every seed, regardless of its subset-bound premise. The matrix never lies in the dummy-k binder's scope. Primitive Bottom aliases can all be false, and optional irreflexivity and same-variable specialization also hold. This is stronger than the older constant-true-universal algebra, which did not satisfy C/G. Adding same-variable specialization alone does not remove this finite-sort obstruction.

**Excluded controls:** original full equality253/254, the profile-control282, the diagnostic-U259/P264 rows, and the full translated-equality348 control are not covered by the raw-calculus theorem. U and P specifically fail the supplied gated instances in this model. Excluding this one model does not prove that either diagnostic is complete or calibrated.

## Code checks and reproduction boundary

I read the countermodel evaluator, 253 regenerator, control-cost generator, verifier, published spec, current edited AX builder, relevant source10/source11 generators, and the PSC adapter/supplement. The 253 regenerator performs the advertised four edits and bijection removing old state8 and checks exact resulting bytes; it repeats a table identity, not the public Coq theorem. The raw252 normalizer fills only the missing `1.inc/read1` action with write1, R, halt before canonical renumbering; this agrees with the documented convention.

Root's already completed run is recorded in `source01-verification.json` and `.log`: PASS in9.62s, seven table checks, exact253/raw252 regeneration, all countermodel cases, U/P witnesses, exact raw252/U259/P264 compiler recipes, all288 sampled control compilations, and seven fixed PSC recipes/core checks. The 288 are 120 bundle layouts per control plus24 row orders for each control's first best bundle, not the full Cartesian product. Broad source hashes were deliberately skipped in memory and final archive hashes were not requested. Optional historical PSC144-order/200-seed searches were not rerun. I did not duplicate those complete suites.

My new independent checks passed: 250 C/G AST comparisons,12 conjunction-variant tree comparisons,16 permuted-rho8 Boolean cases, and eight direct immutable-source byte comparisons. Reproduce with `python /tmp/zfc-review146-7l67s9p4/source01-independent-checks.py`; its small JSON evidence is adjacent.

One current-tree reconciliation point: the paper's pinned83dec statement that the numerical zero alias lacks a formal codec treatment is historical. The present `Base3Syntax.lean` already formalizes total canonical numerical decoding and truth normalization. It does not yet prove this typed semantics, raw-calculus soundness or TM simulation, so it does not alter the substantive obstruction or its literal boundary. No other correction is required for intake.

Durable intake records: data/intake-146-source-12-independent.json, data/intake-146-source-12-verification.json and data/intake-146-source-12-pdf.json preserve the independent checks and full suite result. Scratch paths above identify the review environment, not additional promised repository artifacts. Main finite suites can be recovered with code/reproduce_146.py.
