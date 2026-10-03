# Bounded review of the sparse-lattice editorial transfer

**PASS: no actionable mathematical or scope drift found in the reviewed Part IV additions and README claims.** This review is pinned to commit `bd8a8afd67108107c1fe443e488b84ef05236d78`. All line numbers below refer to that commit, not the current working tree.

The target is `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/`. I read every new `[write]` paragraph in Part IV and the relevant new front matter, question updates and README sections. I compared their claims against the complete WIP review `review_sparse_lattice_aebfa386e.md`, the independent projection review `review_sparse_projection_aebfa.md`, and the maintained projection and five-witness congruence notes. I also read the particular CDC comparison, record-comparator, no-bound, single-fold Presburger and adaptive-support statements cited by the additions. The separate source-occurrence census and Part III review are outside this subtask.

The [pin record](review_signal_typesetting_sparse_editorial.json) records the nine read source objects. The target article has SHA-256 `74a15d44a7cd23d1ffe813bb6d70bd61986bc93a43615504176c2f756505f239`; the README has `ebe0ba2754003afb46f8771399e420c5594edb5f9b1bb605a44b4719ec250201`.

## Resource and representation scope

- Article lines 3011–3015 and 3032–3059 distinguish conserved **numerical mass** `M`, occupied sites, unbounded gaps, and the external horizon `T`. Repeated unit records pay `M`, not merely the number of nonempty sites or the bit length of the masses. The exact full-table witness and residual counts in README lines 411–425 agree with the original review. The quartic is an ordinary integer polynomial for each fixed compiled instance; this does not turn `T` into one more input of a fixed-arity universal polynomial.
- The new front matter makes the same limitation explicit at article lines 338–343 and 365–367, and README lines 344–347 and 454–458. Article line 3691 retains the decisive qualification: arbitrary-horizon universal computation still needs an independently paid compression theorem. The horizon-free result is confined to the decidable mass-at-most-two subclass, after its effective elimination and actual Boolean-circuit size are paid.
- Article line 3693 correctly leaves the adaptive support question open. The displayed `O(T(M²+Mq³))` count pays pairwise tests and sorting, but is not a bound proportional to support plus boundary. It is for one-dimensional partitioned conservative automata, not a sandpile theorem. The cited CDC question actually asks for coordinate, adjacency, sorting and distinctness costs, so this comparison does not omit its main obligation.
- The free-counter-position loader is not an ordinary binary program/data decoder. Article line 343 and README lines 461–463 preserve that distinction. The safe universal source remains an existence construction with no printed numerical state count, while the fully printed doubling example is nonuniversal (article 3013, 3322–3324, 3370 and README 470–476).

## Lower bounds, observations and low mass

- The new editorial no-bound comparison at article line 3429 is accurate: it identifies a shared finite-search argument, not an equality between a bound on orbit diameter and a witness-height bound. The retained proposition at 3421–3427 includes successful-run completeness and permits exact translated-tail decisions for anchored observations. Escaping an arbitrary chosen bound does not itself reject unrestricted later reachability (3414).
- The mass-two exclusion is stated only under the unique zero-weight vacuum and positive-weight hypotheses. Article 3445 describes polynomial time for a **fixed rule** with binary sparse coordinates and an explicitly written target word. Article 3532 separately says that semilinearity is a relation on numerical coordinates, not on digit strings. No resource bound is silently transferred between these representations.
- Article 3518–3520 retains the narrow abstract-level status of the five-particle literature comparison and distinguishes numerical-state particles from multiple internally typed weight-one symbols. Article 367, 3687–3688 and README 472–476 do not claim that three particles suffice, a least universal mass, or a lower bound from the displayed compiler counts.
- The pulse predicate remains an anchored local observation, not global halting or exact-target undecidability (article 3324, 3347, 3441, 3689). The observer means zero detector mass earlier and one now; no editorial claim weakens this to a generic first occurrence of one following arbitrary earlier detector values.

## Editorial comparisons and repairs

The comparison residuals at article 3078 are exactly CDC `cdc:mem:lem:compare`, including its strict offset and tie convention. The two-field compare-exchange at 3135 specializes the cited four-field comparator; the source does not inherit the four-field coordinate count. The note at 3639 accurately compares a degree-four SOS Presburger construction with CDC's degree-at-most-two polynomial nonnegative on the whole real orthant. The cited theorem uses effective quantifier elimination, uniquely evaluated atoms and every Boolean branch; the note neither promotes determinism alone to untimed uniqueness nor claims a single-fold representation of arbitrary c.e. sets. The sign correction note at 3237 accurately reports the earlier primary-source review and does not assert an author-issued erratum.

Article 3680 and README 614–619 correctly identify the one low-level `Poly` constructor defect, the separate tested patch, and the fact that the placed source remains **unpatched**. I checked the actual placed producer bytes at this commit: `code/13-sparse-lattice-sparse_mass.py` has SHA-256 `1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8`, exactly the original producer pin in the full review. The passing theorem and high-level export review is therefore not presented as a repaired public constructor contract.

The same paragraph accurately reports the separately reviewed fixed-initial-configuration projection:

```
V = T[M(S+7)+4M(M−1)],
R = T[10M+4M(M−1)],
removed coordinates and rows = T[7M+M(M−1)].
```

These are the default natural row-selector core counts. They do not include optional endpoint or orthant rows, and the surrounding text supplies the original option costs. The projection keeps quadratic residuals and bijects natural zeros; its independent proof restores nonnegativity at zeros by induction, not on arbitrary tuples. The editorial text correctly calls these variable/row reductions, **not gate counts**. Likewise the five-witness congruence comparison changes `2I+6C+G` to `2I+5C+G` witnesses while retaining the original residual count; it does not price the surrounding eliminated predicate or universal computation.

No change to the universal 87-operation bound follows from these additions. Their useful content remains explicitly separated from that bound.

## Audit limits and reproduction

No report code was imported or executed, no author suite was replayed, and no repository or archive file was modified. This is a bounded editorial-transfer read against completed reviews, not a renewed proof audit of the whole lattice source, new primary-literature search, confirmation of every packaging statement, or PDF/LaTeX verification. The source preservation census is a separate audit.

The pins can be reproduced using read-only Git objects, for example:

```sh
git show bd8a8afd67108107c1fe443e488b84ef05236d78:SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex | sha256sum
```

The companion JSON gives the exact path, Git blob, byte length and SHA-256 for every comparison source. No future commit is included in this PASS.
