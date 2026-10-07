# Integration notes

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `5ea1d06dd2f2d3a30e96016b236e3f1e3dfb048f`.

Suggested new directory:
`Combinatorics/Ramsey/Research/GowersSzemeredi/torsion-exact-restriction/`.

The delivery is a standalone research contribution, not a modification of an
existing formal source. No GitHub write, pull request, or commit was made.

## Theorem interfaces

Theorem 1.1 / Section 5 is the principal generalization of the Lemma 7.5
interface. Inputs are a nonempty graph in `G × H`, finite abelian groups, order
`m ≥ 1`, and graph difference ratio at most `K`. Output is a whole partition of
the domain into exact Freiman cells. Its bound is first stated in terms of the
actual vertical-defect count and then in terms of `K`.

Theorem 1.2 / Section 7 is an arbitrary-group, exact, threshold-free restriction
of high additive relation energy. The selected *same cell* meets both its size
and energy bounds, because the proof chooses a largest cell and bounds its
sumset support.

Corollary 8.1 is the direct cyclic specialization corresponding to Lemma 9.3.
It dominates the original coefficient for `0 < alpha, eta ≤ 1` and permits
`N0 = 1`. The pinned repository already contains `lemma_9_3_holds`; retain that
fact in any summary. The result is a stronger alternative theorem, not a new
claim about the repository's compilation status.

Corollary 8.2 is the direct energy version of the Corollary 9.4 interface. In the
cyclic normalization `|B| = beta N`, the input is graph energy at least
`gamma beta^3 N^3 = gamma |B|^3`. The output has no extra `beta^6` factor inside
its energy-retention coefficient.

Theorem 1.3 / Section 9 solves the leading-order exponent problem for the
explicitly defined avoidance-coloring invariant. It is not a claim that a
previously named conjecture has been settled. Distinguish it from the graph
extraction exponent, for which a substantial gap remains.

## Avoiding duplication and overstatement

The inspected research README records prime-field order-eight size bounds much
better than the universal size constant here. The `alpha^911` size guarantee
must not be described as stronger than `gamma^103` under the latter's matching
prime-field hypothesis.

The standard energy-to-growth argument in Section 6 is background. It was
included to make the numerical combination independent of unverified research
inputs. Section 7.1 provides a modular substitution formula for stronger inputs.
When using it, first convert any difference-set bound relative to the original
size into a ratio relative to the selected core size.

No theorem here keeps a complete derivative spectrum or cross-section
compatibility. Preservation of one prescribed scalar sum is strictly weaker.
No change to a global Szemerédi bound follows from this package alone.

## Merge mechanics

The TeX file is self-contained, with an inline bibliography and labels prefixed
`ter:`. For a combined research volume, move the body after the title/contents
into the desired chapter and merge the explicitly listed packages and macros.
Generic theorem environments may need to be adapted to the volume's own
numbering. Preserve the source/provenance and limitation paragraphs.

The Python programs use only the standard library and have no external data.
They can be placed beside the article or under a research-checks subdirectory.
No `.lean` file is supplied, and the formalization ledger should remain
unchanged until a separate checked proof is integrated.
