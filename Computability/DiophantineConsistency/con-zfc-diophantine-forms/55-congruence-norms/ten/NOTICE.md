# Attribution and provenance

This is a new finalizer and source adapter built on ProveIt's existing
Diophantine consistency construction. The 31-positive-variable parent, its
coefficient tuple, the selective-support source code, sparse-borrow masks,
population calibration, and the quintic divisibility merger are inherited.
The arithmetic DAG class is adapted from the repository's earlier packages.
The Lucas bridge and residue interpolation are due to Zhi-Wei Sun, as cited
in `PROOF.md`.

The immediate input is
`docs/incoming/ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` at repository
commit `4b4349064a750ba6347293b55874a7f92abdd0db`, component
`packing/mask_popcount`. `INHERITED_SOURCE.json` records the archive hash.
`SOURCE_PINS.json` is preserved as the historical chain of exact hashes for
the parent, coefficient tuple, proofs, and licenses copied by that package;
its older commit is not a claim that the new finalizer existed at that commit.

This iteration contributes: an unshifted positive source packed through the
common word shift; the two repaired support targets needed for that source;
a coprime square-product seed; a Pell guard recovering positivity and the
otherwise necessary nonvanishing of the bridge variable; congruence-preserving
normalizations of the constructive bridge; and a two-root finalizer whose
radicands are separated by parity after division by a nonzero common factor.
The latter quotient is used only in the proof: the emitted polynomial is
division-free. The package also supplies independently computed source,
arithmetic, and exact-degree certificates.

The files in `licenses/` retain their upstream terms. New report, scripts and
certificates are prepared for incorporation in ProveIt. This notice does not
supersede third-party licenses. Preserved upstream prose is not a claim of a
new end-to-end formal proof. Neither the number of variables nor global
minimality is claimed as a new result.
