# Logical calibration and source experiments at K218

Pinned upstream revision: `704b87442afbd571833a628cd558f1d207fd8b2f`.

This note records completed mathematical work and reproducible source experiments. It does **not** assert the existence of a verified 217-state machine. The tempting deletion of scanner state 50 has a valid logical seed, but fails a required physical primitive contract. None of the source experiments below supplies a replacement physical proof.

## 1. The exact optimization target

The accepted native K218 table has 218 working states, a source tree with 4744 primitive occurrences and 205 distinct subtree nodes, maximum source depth 38, and maximum consecutive left-edge run 6. The source-node count is an optimization proxy, not the number of working states. Contextual decoder aliases, two roles of a shared physical state, primitive helpers, complete blank startup, and arbitrary clean-frame runtime must all survive a proposed reduction.

The native formula coding uses Cantor pairing

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b
\]

and constructors

\[
I(a,b)=4P(a,b),\quad R(a,b)=4P(a,b)+1,\quad
Q_a b=4P(a,b)+2,\quad E(a,b)=4P(a,b)+3.
\]

The truth alias is 0, the falsity code is 1, negation is `I(A,1)`, and existential quantification is `N(Q_i(N A))`. All natural numbers are legitimate formula codes; object-variable labels are also arbitrary natural numbers. In particular, a code transformation must act coherently on formula arguments **and** labels. Restricting attention to a familiar syntactic subset can silently lose the calibration theorem.

The two retained logical rows most sensitive to attempted simplification are the unrestricted four-parameter classical axiom

\[
((C\to U)\to A)\to((A\to C)\to(B\to C))
\]

and the gated bundle, emitted for every `c != a,b`. The latter carries both the set-theoretic comprehension component and atomic membership vacuity

\[
R(a,b)\to Q_c R(a,b).
\]

An apparently harmless restriction on the bundle therefore changes the available quantifier logic as well as the set-theoretic axiom family.

## 2. A rechecked clean-seed theorem, with no consistency assumption

The general seed theorem and the cofinal `START_U` argument are already present in the pinned upstream note [*General logical seeds for the 218 startup search*](https://github.com/VladimirReshetnikov/ProveIt/blob/704b87442afbd571833a628cd558f1d207fd8b2f/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/146-r218-res-src218-general_seed_lemma.md), which also credits an earlier K224 adaptation. The contribution here is an independent check against the exact maintained source interfaces, its specialization to current formula 3, and a portable independently replayed equality certificate; discovery of the general theorem is not claimed.

### Statement

Let an abstract enumerator state have a derivable current formula `tw`, a derivable cache `h`, and a theorem-valued stack `ws`. The candidate counter `np`, additive parameter `d`, and remaining proof-list pointer `pl` may be arbitrary natural numbers. Then

\[
\operatorname{Halts}(s)\quad\Longleftrightarrow\quad C_{222}(1).
\]

This is an ordinary finite-proof statement. Neither direction assumes `Con(ZFC)`. Together with the inherited finite-refutation calibration and a correct source-to-machine simulation it gives the desired equivalence at any such clean seed.

### Soundness

The upstream invariant is exactly

\[
C_{222}(\mathrm{tw})\;\land\;C_{222}(\mathrm h)\;\land\;\operatorname{Good}(\mathrm{ws}).
\]

It imposes no restriction on `np,d,pl`. Each command preserves the invariant. Only NIP halts; its halting branch requires the cache to equal falsity. Thus any finite halting run yields a finite native derivation of 1. This argument is already universal in the initial working state.

### Completeness beyond a finite candidate cutoff

The existing proof compiler gives, from any derivation of 1, a finite command list `p` satisfying its uniform contract: for every current formula `T` and every stack `S`, execution from `(tw,ws,d,h)=(T,S,0,0)` either halts or returns `(1,S,0,0)`.

Prepend the command

\[
\mathrm{START}_U=\mathrm{AX}(c=0,x=1,y=1,u=U).
\]

Its literal command equation resets `d=h=0`, regardless of their previous values. Append `DROP(0),NIP(0),NIP(0)` to `p`. If `p` has not already halted, this suffix pushes 1, loads 1 into the cache, and halts. Therefore this complete command list halts from every working tuple.

Let `r` be one plus the candidate encoding of the fixed nonempty suffix. The candidate number of the complete list is

\[
N_U=P(3,P(1,P(1,P(U,r)))).
\]

Since pairing is at least either argument, `N_U >= U`. Choose `U >= np`. Every positive proof-list pointer strictly decreases during a nonhalting command; a list boundary starts the next candidate and increases the counter by one. An initial partial list first drains without changing the counter. Consequently the run either halts earlier or eventually starts candidate `N_U` and halts there. This proves completeness for every finite cutoff.

The exact source representation is

\[
\operatorname{toAS}(s)=[np,tw,ws,0,d,h,0,0,pl].
\]

The inspected source correspondence is universal in `s`; it does not require the historical bootstrap values. A clean source root therefore needs no special protected-tail argument.

### The scanner deletion's seed is admissible

Deleting physical scanner state 50 and changing the zero transition of state 34 from `0 L 50` to `0 L 75` was observed independently by the machine workstream to reach

\[
[np,tw,ws,ac,d,h,s_1,s_2,pl]=[4,3,0,0,3,0,0,0,0].
\]

Here 3 is `E(0,0)`, not `I(0,0)`. Equality reflexivity is derivable from the retained merged equality row, rho1, rho2, rho6, theorem-only generalization, and the propositional basis. Thus `tw=3` is a theorem; `h=0` and the empty stack satisfy the invariant, and the cutoff/additive values are harmless by the theorem above.

For a useful explicit derivation, write `r=R(x,x)` and `X=E(r,x)`. The merged equality row gives `X -> (X -> Q_r E(x,x))`; propositional contraction gives `X -> Q_r E(x,x)`. Generalization and rho2 give existential monotonicity, hence `Ex_r X -> Ex_r Q_r E(x,x)`. Rho1 proves `Ex_r X`; rho6 proves `Ex_r Q_r E(x,x) -> E(x,x)`. Two modus ponens steps finish. At `x=0` the conclusion is native code 3.

A closed 79-node certificate for this derivation is included, together with an independent checker. The upstream generator constructs 96 nodes before unused nodes are removed. The checker verifies literal axiom shapes, topological premise references, modus ponens, and closed-theorem generalization. K and S are treated as the already proved consequences of the unrestricted native classical row; their derivations from that row are inherited, not newly expanded by this certificate. No new Lean or Rocq theorem is claimed to have compiled.

The physical deletion remains rejected: its arbitrary-clean-frame CD1 zero case can create a transient seven-zero run even though the static source-path maximum is six. Logical admissibility of the new seed does not repair that failure.

## 3. Calibrated transformations that were priced

### Independent parameter renaming and row ordering

Every complete axiom schema is emitted over all natural parameters. Independently permuting `(a,b,c)` within such a complete row leaves the native axiom family unchanged. For the bundle, only exchanging `a,b` was used, keeping its private field `c` and gate synchronized. The unrestricted classical row retains its separate fourth parameter `U`.

The eight unconditional schema rows can also be reordered as whole outputs. They read stable parameters and push the same finite collection of theorem instances; the one extraction of `U` moves with its own row. The generalized cached theorem and gated final bundle remain in their original roles. Soundness is unchanged, and the proof compiler can select the relocated stack entries. This requires the corresponding stack-index update when turning a source experiment into a complete formal enumerator proof; no binary runtime certificate is claimed for a reordered source here.

The fixed source scaffold was exhaustively tested for all `8! = 40320` row orders. None reduced 205 source DAG nodes. A separate bounded beam search tested 81208 independent field-assignment profiles and likewise found no reduction below 205. These are finite experiment results, not lower bounds over all encodings.

### The dual of rho6

The ordinary row

\[
L_i(A):\quad \neg Q_i\neg Q_i A\to A
\]

may be replaced by

\[
D_i(A):\quad A\to Q_i\neg Q_i\neg A.
\]

The two full schemas are interderivable with the unchanged classical basis, rho2, and theorem-only generalization. From `L_i(neg A)`, classical contraposition and double-negation elimination give `D_i(A)`. Conversely, apply `D_i` to `neg A`; lift the classical theorem `neg neg A <-> A` through the required quantifiers using rho2 and theorem generalization, and contrapose. This gives `L_i(A)`. The conversions are finite derivation transformations uniform in all native codes and do not assume quantified stability as an additional axiom.

The in-place scaffold costs 207 nodes for the best dual variant. An exhaustive one-hole parenthesization search of 201552 cases found a 206-node dual source, but its maximum zero run is 7. The unchanged row also costs 207 when constrained to that one-hole representation: the representation itself loses useful sharing across the row boundary. These figures therefore must not be compared as if one-hole substitution preserved the baseline 205-node grammar.

### Nonzero-tag permutations and implication orientation

If implication keeps tag 0, any permutation of the three nonzero constructor tags is an exact code conjugacy. The same is true of reversing the two arguments of the implication constructor, provided the MP matcher reverses its pair as well. Define the translation recursively on every positive natural code, translate both constructor arguments including object labels, and set `tau(0)=0`. Every positive code has strictly smaller Cantor components; the translation and its inverse are therefore well founded. It preserves gate inequalities, the merged row's label `R(a,b)`, and the self-coded private field of the bundle. Finite derivations translate in both directions, and falsity translates to the new membership tag.

This is stronger than a relabeling of familiar formula syntax: it covers all natural-code junk and all numeric labels. It is the appropriate reason these transformations preserve the consistency calibration.

All six nonzero-tag permutations were priced in 87 local literal layouts; identity remained best at 205 nodes. Extending the source census to all 18 tag assignments with a nonzero membership falsity gave 183 layouts and no improvement. The assignments with zero equality or zero universal-quantifier tag are **not** covered by the preceding exact-conjugacy proof: the special zero alias changes, and a separate interpretation argument would be needed. Those additional cases were only source prices, and their best nonidentity cost was 206 with excessive zero runs.

Reversing implication changes many postfix word patterns. Keeping the old macro scaffold gave 273 nodes before the MP correction and 277 after it. A 75-second bounded grammar reconstruction tested 2609 layouts and reduced that cost to 219 nodes, with maximum zero run 12. No tested reconstructed layout had maximum zero run at most six. The grammar reconstruction is heuristic and proves no lower bound.

### Direct MP pairers

The usual source emits the candidate implication by a push-copy of the target and a generic implication macro. It uses 53 primitive occurrences. Two direct arithmetic implementations were found:

* Reversed implication: copy register 4 into zero register 6 while preserving 4 via zero register 7, then run the existing pair-and-scale macro. This computes `4P(B,T)` in register 1 using 23 leaves and preserves the theorem stack.
* Ordinary implication: move register 1 into zero register 6, copy register 4 back into 1 via zero register 7, and use the same pair-and-scale macro. This computes `4P(T,B)` using 26 leaves.

The copies are elementary unary loops. The reversed copy is

```
((CD4,(CI7,(CI6,CC3))),(CD7,(CI4,CC2))).
```

Finite source checks cover 147 input stencils for each pairer and compare every register. Their general arithmetic contracts follow by the two counted loops and the inherited pair-and-scale contract; no new physical macro verification is asserted. Despite eliminating many primitive occurrences, the ordinary direct pairer increases the full grammar from 205 to 212 nodes. This is a concrete example of a leaf-count saving that loses at the shared-state level.

### Alternative classical bases

Two standard complete classical implicational bases were priced after removing the unrestricted four-parameter row and its fourth-field extraction: K/B/Peirce and K/S/Peirce. Each family was tested in 3888 fixed-layout combinations of field assignments, row orders, and top-level associations. Minimum costs were 210 and 212 nodes, respectively. No claim is made that these searches cover all short classical bases or all source layouts.

## 4. New gate-removal ideas and the unresolved logical obstruction

### Constructor wrappers

The gate tests `c != a,b` because the bundle needs a fresh private numeric label. One might replace `c` by a larger code, then emit the bundle unconditionally. Two proposed wrappers are

\[
k=I(Q_a b,c),\qquad k=Q_{I(a,b)}c.
\]

Both are strictly greater than `a,b,c`, including the all-zero case. The first uses the positivity of the quantifier tag; the second has an outer positive quantifier tag. Thus each wrapped axiom is a valid old bundle instance, and soundness as a subsystem is immediate. In contrast, `I(a,I(b,c))` is not fresh at the all-zero input and cannot remove the gate without another guard.

There are plausible translations for the set-theoretic matrix component. For the first wrapper, renaming numeric labels to codes of the form `I(l,l)` makes the decoded antecedent tautological. For the second, renaming all ordinary object labels into the membership-tag alphabet makes the extra implication-tag binder absent from the translated matrix, so its outer quantifier is vacuous.

These observations are **not a calibration proof**. The same bundle supplies atomic vacuity. After wrapping, the available vacuity instances are only

\[
R(a,b)\to Q_{k(a,b,c)}R(a,b).
\]

The constructor's injectivity makes the available binder ranges for different pairs `(a,b)` largely disjoint. The inherited equality-by-indiscernibility interpretation explicitly needs unrestricted atomic vacuity for all distinct labels. A finite formula containing several atoms needs a common supply of usable fresh binders; semantic harmlessness of the wrapped matrix does not supply that. No proof of equiconsistency was obtained for either wrapper calculus.

The source prices were also unfavorable. Replacing all 13 private-field reads by a shared wrapper and replacing the gate by the necessary register cleanup gave a minimum 209 nodes among 672 layouts. Precomputing the wrapper once and restoring the current theorem/stack gave 211 nodes among 144 representative complete layouts. Neither result is a calibrated candidate.

### Cofinite freshness

A better logical version is

\[
k=a+b+c+1.
\]

For each fixed atom `R(a,b)`, varying `c` makes every sufficiently large binder available. For any finite set of atoms the permitted binder sets therefore have a common cofinite intersection. This removes the disjoint-range obstruction of the constructor wrappers and suggests a locally finite cylindric or Henkin-style completeness argument.

That argument remains open. A single global renaming of all variable labels does not suffice: requiring a binder above the sum of an atom's two labels can yield incompatible inequalities when different variables serve alternately as binders and arguments. For example, demands involving `R(x,z)` under `y` and `R(y,z)` under `x` would force both `y>x+z` and `x>y+z`. A proof must change the finite derivation or build a suitable model interpretation; it cannot simply assert that all finitely many labels can be made large.

There is also a semantic support issue: high-label atomic vacuity alone does not establish that an atom depends only on its two displayed coordinates. A relation interpreted as ordinary membership conjoined with a predicate of one low coordinate illustrates the missing inference. This observation is not a countermodel to the complete proposed set-theoretic theory; it identifies why the existing completeness proof cannot be reused unchanged.

## 5. Alternative physical layouts of the unbooted core

At the end of the investigation, the inherited zero-terminal, retagged, and composed K219 patches were transferred to the runtime-correct but unbooted core217. The corresponding K218 source variants all retain 205 distinct source nodes. The published alternative tables use normalized labels 102 and 120, so literal differences must instead be taken from their `upstream-labels` versions. The deleted 301/1 patch is omitted only after checking that both its old and new actions coincide with the retained 88/1 branch.

All three transferred tables, and each one's optional row157 alternative, have 217 states, 434 rows, and a valid decoder-prefix/source binding. Direct blank execution from all 217 working initial states still reaches provable blank rays for all six tables. No unbounded runtime claim was made for these transferred variants: their literal initialization already fails.

The three base variants were then searched under physical source rotations. The depth-eight search was exhaustive **within its stated traversal**: each next rotation must touch a transition used by the current start 0 blank prefix; every resulting layout is tested from all 217 initial states, with the engine's ray reuse and depth-aware deduplication. Each variant produced exactly the following receipt:

| Quantity | Value |
| --- | ---: |
| Maximum rotation depth |8 |
| Accepted traversal visits |4579 |
| Distinct stored layout/source keys |4241 |
| Required blank-start runs |62324 |
| Complete source frames found |0 |
| Maximum final finite support |8 |
| Traversal status |Complete |

Separate depth-sixteen runs stopped at their 90-second bounds. They visited 11099,10912, and10169 layouts for zero-terminal, retagged, and composed respectively, with no frame. They are not described as exhaustive. Neither the shallow exhaustion nor the stopped deep runs rules out arbitrary coordinated source-layout changes.

The standalone `rebuild_core_variants.py` reconstructs all six literal tables from the pinned core alone, using the inherited checked patch data. Every output was compared byte-for-byte to the table used in these searches. The source sidecars and depth-eight receipts are included; the archive's portable rotation engine can replay the searches directly with `--table`, `--sites`, `--active-start0`, and `--depth 8`.

## 6. Reproduction and trust boundaries

All scripts are standard-library Python. Their default relative layout expects this note and the scripts in `research/formalism`, with the following minimal upstream files at `research/ProveIt/Computability/BusyBeaver/Research/ZFC/`:

* `candidate-k218/sites218.json`;
* `candidate-k218/k218.native.tm`;
* `k218-quantifier-stability/pricing/source_language.py`;
* `k218-quantifier-stability/pricing/build221.py`;
* `k218-quantifier-stability/pricing/measure_pinned.py`.

Recreating the seed certificate additionally uses `k218-quantifier-stability/check_derivation.py`. Checking the included seed certificate needs no upstream files:

```
python3 replay_seed3.py --check-only seed3-certificate/seed3-proof.json --output checked-seed3
```

The source census scripts read literal pinned table/source files. The paired source-graph resolvers check the generated tree's control-flow interpretation; they do not certify binary execution. The exploratory allocator checks decoder prefix behavior and can reject a grammatically attractive source because a contextual alias no longer has its required prefix. A successful allocation would still leave complete startup and arbitrary-register runtime obligations.

The two main source inputs have SHA256 digests:

```
sites218.json   b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9
k218.native.tm  2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f
```

The independently checked seed proof has SHA256

```
d6fdd2a43fdf255e8b7a3ca3c16cbaec8f7a2730e7be9b3df2c2bc803a91e052
```

The logical results above are useful reusable lemmas and calibrated search directions. They are not a substitute for an accepted 217-state runtime certificate.

### Reproduction entry point and references

For the selected fast census and MP checks, run

```
python3 reproduce_formalism.py --upstream /path/to/ProveIt --experiment core
```

The argument can also name the `Research/ZFC` directory directly. `--verify-only` checks all five pinned dependencies and replays the independent seed certificate. The groups `classical`, `dual`, `fields`, `wrappers`, and `implication` reproduce the corresponding larger searches; `all` runs every selected group. The time-bounded heuristic runs can evaluate different numbers of trials on different computers, so their exact historical receipts remain separate from a fresh replay.

The mathematical interfaces were inspected in the following files at the pinned commit: `Code254.lean` for native constructors, `KCode222.lean` for the retained calculus, `KEqCodes222.lean` for equality reflexivity, `Enum222.lean` for the stack invariant and uniform command compiler, `L2Root219.lean` for the universal source-root map, and `KEind222.lean` for the use of atomic membership vacuity in the equality-by-indiscernibility interpretation. These are in [the repository's Lean ZFC directory](https://github.com/VladimirReshetnikov/ProveIt/tree/704b87442afbd571833a628cd558f1d207fd8b2f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC).

The K/B/Peirce basis is the Bernays–Tarski system described in Frank Pfenning's [*Single Axioms in the Implicational Propositional Calculus*](https://www.cs.cmu.edu/~fp/papers/cade88.pdf), section2.1. A formal development of the same basis is [*Implicational Logic* in the Archive of Formal Proofs](https://isa-afp.org/browser_info/current/AFP/Implicational_Logic/Implicational_Logic.html). These references justify the classical basis comparison; they do not supply any source-runtime claim.
