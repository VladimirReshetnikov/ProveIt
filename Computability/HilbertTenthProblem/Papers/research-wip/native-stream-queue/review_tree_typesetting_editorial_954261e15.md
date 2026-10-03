# Bounded editorial review: Tree Calculus integration 954261e15

Reviewed commit `954261e15e38d84bdb2e1a97d93097a6b5551d5a`, specifically the new introduction summary, Part XIX opening and conventions, comparisons with the older Parts, no-computable-bound note, formalization remark, research-question annotations and corresponding README scientific summaries. The complete source-preservation census belongs to the parent review. No unchanged author suite, full historical theorem audit, PDF rendering or proof-assistant build was repeated. No repository file or archive was changed.

The three issues identified by the parent are confirmed. One additional editorial implication needs a hypothesis. These findings concern new framing; they do not contradict the prior review's conclusion that the original eager construction had no theorem-level defect.

## Findings

1. **P2 — preserve the input-translation obligation in the single-fold comparison.** `article.tex:31441` newly says that, by `cdc:bd:thm:universal`, a fixed-arity single-fold representation “for the universal tree” would settle the general single-fold problem. The supplied theorem for the fixed tree only proves that `H_U` is complete under **computable many-one reductions** (`article.tex:31047–31060`). Its reduction is `m ↦ code(C(Q(m)))`. The original loader section explicitly says its arithmetic graph is not supplied (`article.tex:31103–31115`; original source lines649–662).

   The cited Part IX implication instead specializes a polynomial `H(e,x,w)` at the fixed program index `e_A`, keeping the ordinary input coordinate `x` (`article.tex:8987–8989`). An arbitrary computable substitution is not a polynomial substitution; representing its graph by an ordinary Diophantine formula does not by itself preserve single-foldness. The new sentence therefore does not follow from the premises cited there. This is a missing proof obligation, not a counterexample to the existence of a suitable translation.

   Suggested replacement: “A fixed-arity single-fold representation for the universal tree, **together with a fully charged single-fold input translation from universal halting**, would settle the open single-fold problem.” Equivalently, formulate the premise directly as a single-fold representation of universal halting on ordinary `(e,x)` parameters. If the translation has one natural extension `(n,u)` for each `(e,x)` and the tree polynomial has one witness on each accepted `n`, a sum of squares composes them while preserving the unique fiber, and Part IX then applies.

2. **P3 — the README opening must select the canonical exact-size variant.** `README.md:21–24` promises exactly one witness across all twenty-one sources. Its new source21 description at lines39–41 only supplies an external bound on distinct calls. That is the base family's `D≤N` interface, whose fibers are nonunique even at `N=1`. The original source's “Fibers are not unique” remark gives an explicit one-row example: `E(0,5,11)` permits arbitrarily large unused `(a,b,c,u,v)`, with the candidate fields recomputed (original line361). Canonical uniqueness instead holds at `N=D` and cannot be padded (`article.tex:31201–31203`).

   Specify in the opening that source21's one-witness claim refers to its **canonical refinement at the exact number of distinct calls**, while its base upper-bound family allows nonunique witnesses. The new contribution list at README422–445 and the later scope section at README1845–1864 already make the correct distinction.

3. **P3 — the Part XIX preface drops the affine size formula's threshold.** `article.tex:30530` says the fixed program `R` has exact canonical DAG size `64n+113`, without `n≥2`. The actual theorem, correctly preserved at line31277, is `D_0=44`, `D_1=179`, and `D_n=64n+113` for `n≥2`. The unrestricted affine expression would give113 and177 in the two base cases. Add the threshold and preferably the base values. The original source821, the new introduction at3112 and README444–445 retain them correctly.

4. **P3 — two current collection counts are stale.** `article.tex:31907` opens the provenance appendix with “built from twenty manuscripts”; `article.tex:32018` opens the bibliography with “for the twenty manuscripts”. Both should say twenty-one. The phrase at README937 is different: it describes the previous cluster-J3 write and its then-retitled heading, so its historical twenty is correct and should remain.

## Other new scientific framing checked

The new **no-computable-bound** note at article31116 is supported. For a fixed input and fixed `N`, evaluate the eager kernel with memoization, reject a repeated active call, and reject on discovery of the `(N+1)`st distinct pair. Successful calls can be reused. A finite execution uses at most `N` distinct pairs; any attempted infinite computation confined to those pairs must repeat an active pair, because the deterministic kernel's finite-branching call stack cannot keep growing through distinct pairs. Thus bounded distinct-call acceptance is decidable. A *total* computable input-wise bound valid on the halting domain would decide the stated r.e.-complete `H_U`. This argument concerns the present bounded family; it is not an impossibility theorem for arbitrary fixed-arity MRDP representations.

The new formalization remark at article30947–30949 and README2313–2332 correctly separates the local forward contextual-beta simulations into SK/SKI/Iota from the unformalized eager Tree Calculus theorem that reflects termination. I checked the named Lean/Rocq declarations and the local combinatory-logic README at the same pinned commit. The comparison does not silently identify the vendored weak-CBV calculus `L` with the local contextual-beta model or claim that the new eager proof is kernel checked. This is a source/declaration read, not a new formal build.

The constructor-pairing, inactive-branch, scheduled-SKI and memory/DAG comparisons retain the different computational objects. In particular, the Part XIX opening explicitly acknowledges nonunique base fibers, exact-size canonical uniqueness, natural-only coordinates, growing arity, gigantic fixed scalar codes, and unpaid input translation. The memory-log comparison proposes a possible addressing backend without claiming that it already lowers this compiler's selector cost. The new review disclosures agree with `review_eager_tree_aebfa.md`, including the unapplied evaluator-boundary patch, the literal counts, the refined `R` bit interval, and the distinction between proofs and finite tests.

## Pins and reproduction

The accompanying JSON records every consulted source pin and the exact finding locations. Main SHA-256 values:

- Committed `article.tex`: `594e3da5caf4aac5228e594ed30feb506746c51d8d7896157934ed2566a38bb7`.
- Committed `README.md`: `6c5a1a81931914f9caaff22c3a02dcd2a5c45d28f279718d8e96b358ffb3df8d`.
- Original archive at `aebfa386e`: `5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4`.
- Original `eager-tree-certificates.tex`: `196e6fbebcdeceaa81c3356682ef5325b0a4faae093167414465f30371e92c31`.
- Prior full review at the reviewed commit: `a8a5ff72f4e90ccb461ec77339653c4613d65dc7fc40ff98445370ee13e4ff6d`.

Reproduce the reviewed boundary with read-only Git:

```sh
git diff --unified=2 954261e15^ 954261e15 -- \
  SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex \
  SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md
git show aebfa386e:docs/incoming/Eager_Tree_Calculus_Research_Package.zip > /tmp/eager-original-review.zip
```

Line numbers above refer to the committed text at `954261e15`, not future revisions. The PDF is pinned in the receipt only as an unchanged revision boundary; this review makes no new rendering claim. Proposed wording is review advice, not an applied correction or a regenerated PDF.
