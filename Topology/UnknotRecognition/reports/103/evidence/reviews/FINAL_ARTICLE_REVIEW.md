# Final article review: Sections 04–06

12 October 2026. This review covers the current article files
`04_joint_forests.tex`, `05_chain_constraint.tex`,
`06_exceptional_kernel.tex`, and the research implementation
`fast/core_top_research/residual_kernel.py`. No optional tests were run.
No production or article files were edited during this review.

## Verdict

The exceptional-row kernel theorem, its complete stopping-family statement,
its largest-fibre lift, and its constructive source peeling prefix are sound
under the stated assumption that the selected short-row graph is a forest.
The implementation follows these statements. No counterexample or correctness
defect was found. Sections 04 and 05 are mathematically consistent with Section
06 and correctly distinguish abstract graph data from authenticated geometry.

One explanatory sentence would strengthen the constructive proof; two local
notation choices could be made clearer. Neither is a mathematical blocker.

## 1. Stopping projection: why the ground is different

For a subset R of exceptional rows, the quotient column of a free short-tree
component has sum one exactly when the entire component contains one active
exceptional occurrence, of coefficient one. Saturation at either stage does
not change this predicate.

Such a component cannot support a stopping extension. If the unique incidence
site is isolated in the selected short-edge subforest, it has source column sum
one. Otherwise its selected tree has another leaf with no exceptional incidence,
also of column sum one. This proves the required projection condition, including
selected subforests with several components.

There is no analogous condition on the grounded component. Ground is not a
matrix column and may be a terminal leaf of a selected path. One exceptional
occurrence at a column can be supported by the entire path from that column to
ground. Omitting the grounded quotient column is therefore necessary, not merely
a convention. The article's two-row example correctly demonstrates the error
that retaining it would cause.

## 2. The largest lift is the minimal marked subtree

For any source stopping set P projecting to R, every nonground leaf of a
nontrivial component of its selected short-edge subforest must have positive
R-incidence. Ground is additionally marked. Every selected short edge lies on
the unique path between two leaves of its selected tree, hence belongs to the
minimal subtree spanning these marked sites in the original short forest.
Thus P is contained in R union T(R).

Conversely, if R stops in the quotient, all column sums of R union T(R) are
zero or at least two:

- An internal subtree vertex has at least two selected short incidences.
- A nonground subtree leaf has one short incidence and at least one exceptional
  incidence.
- A marked column isolated in the selected subtree must be the only marked
  site in a free component. Its aggregate exceptional incidence is at least
  two, by the quotient stopping condition.
- An unmarked isolated column has sum zero. Ground imposes no condition.

This proves both existence and uniqueness of the largest extension in each
stopping fibre. Monotonicity of the marked-site set and of the union of unique
tree paths gives the claimed formula for the canonical largest source stopping
set. The argument uses nonnegative counts, not signed or parity incidences.

## 3. Important edge cases checked mathematically

**Empty projection.** With R empty, only ground is marked and T(R) has no edges.
There is no nonempty stopping subset consisting solely of forest edges. The
empty stopping set convention is therefore consistent.

**Zero exceptional rows.** They remain zero quotient rows and are stopping by
themselves. Deleting such rows during compression would be unsound; the article
and implementation correctly retain them.

**A single marked site with multiple occurrences.** Two occurrences at the same
site in a free component need no supporting short edges. The minimal subtree
has empty edge set and the exceptional row set already stops at that site.
Two unit occurrences at different sites instead force the path between them.
The quotient correctly counts occurrences rather than distinct incidence sites.

**Grounded components with one exceptional site.** The maximal lift includes
the path to ground even when the exceptional coefficient is already at least
two. Adding any further unmarked branch would create an unsupported nonground
leaf, so the stated largest lift remains exact.

**Isolated columns.** Columns appearing only in exceptional rows become isolated
free components, which is necessary. The sparse implementation includes them
because it gathers column labels from all rows. Completely zero columns can be
omitted without changing any stopping predicate.

**Short loops and parallel-edge cycles.** The forest hypothesis excludes them.
The early implementation branch returns a valid short-cycle stopping witness;
it does not purport to compute the full canonical source stopping set in that
branch. Descriptions of exact canonical residual recovery should remain scoped
to the forest branch, as the theorem currently does.

**No exceptional rows.** The quotient has zero rows and zero nonzero patterns.
The remaining short forest peels completely, including its grounded component.
The bound `3^k - 1` correctly gives zero when k is zero.

## 4. Lifted source prefixes, including duplicate quotient columns

At a quotient pivot (e,K), exactly one active exceptional source incidence lies
in the chosen free component K. Its coefficient is one. Pruning the short tree
toward that site removes nonground leaves whose only active source incidence
is their single short edge. Every such source pair is therefore a unit-column
pivot. Once these edges are removed, (e,c) is also a valid source pivot.

The following invariant is worth stating explicitly in the article:

> Once a component is used for a quotient pivot, its unique active exceptional
> incidence is removed. It has no remaining or future active exceptional
> incidences, so none of the short edges pruned there can belong to the final
> marked subtree T(R_*).

This proves that the earlier lifted prefix has not removed an edge needed for
the final canonical obstruction. Components not yet used keep their short
trees until the final unmarked-leaf pruning. A used quotient component cannot
be used for a later pivot, because its quotient column becomes zero.

Duplicate-column compression preserves this invariant. Equal full signatures
have equal sums on every later active exceptional-row subset. A unit pivot in
the compressed column therefore lifts through its retained representative
component. Removing its row simultaneously removes the corresponding
exceptional incidences in other identical components; those other short trees
may simply be peeled later. No multiplication by the number of duplicate
columns is appropriate or performed.

The final unmarked nonground-leaf pruning leaves precisely T(R_*). Checking all
source pivots against unchanged input rows and checking that the final residual
has no unit column certifies a maximal prefix and, by stopping persistence, the
canonical source stopping set. The implementation's source labels and counts
are consistent with this no-fill interpretation.

## 5. Pattern compression and complexity scope

The column-pattern corollary preserves the whole stopping family because a
repeated column repeats exactly the same unit-sum predicate on every row subset.
Zero columns impose no predicate. Rows, including zero rows, are preserved.
The at-most-`3^k-1` bound is exact as a counting bound on possible nonzero ternary
signatures; it does not require enumerating all signatures.

The article correctly separates linear graph preprocessing from the supplied
prototype's direct scans during lifting and dense signature sorting. It also
correctly distinguishes the bounded quotient matrix from the larger source
forest and incidence maps needed for lifting. There is no claimed improvement
over linear sparse peeling for one explicit matrix, and no unsupported bound
on k or on updating the kernel after changing forests.

## 6. Cross-section notation and claim consistency

The references `sec:joint`, `lem:graphic`, `prop:not-matroid`, `sec:chain`,
`thm:mandatory-chain`, and the new kernel labels are consistent in the files
read. The rooted/top relative results are invoked in the correct direction.

Minor editorial suggestions:

1. Section 05 uses A for the binary occurrence matrix, while Section 06 explicitly
   redefines A as nonnegative. A brief reminder at the beginning of Section 06
   would prevent readers from carrying over the field convention.
2. Section 06's final complexity subsection reuses q for the number of free
   components, after q denoted three-handles in the previous sections. Renaming
   that local number, for example to f, would reduce avoidable ambiguity.
3. Sections 04 and 05 both state the same abstract nonrealizable exchange example.
   This is mathematically harmless; the author can replace the repetition in 05
   by a reference plus its explicit binary matrices if tighter exposition is
   desired.

The geometric family added to Section 05 is sound: the attaching curves are
primitive longitudes of the first solid torus and meridians of its complementary
solid torus. Its genuine multiple-tree examples do not contradict invariance,
and its nonempty-boundary condition keeps the cap-incidence rank full.

No theorem revision is required on the basis of this review.
