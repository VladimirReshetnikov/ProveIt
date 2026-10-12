# Incoming geometry audit and extension rationale

The work used the pinned current repository at
`a28a49ee5c4145db0facbeb1e7f65cd8a2816775` and the extracted incoming
marked-parallelity, interface-homology, corner-aware, and four-copy packages.
Native execution used the exact marked-parallelity incoming runtime, with its
module hashes retained in `evidence/upstream_dependencies.json`.

The inspection did not establish a false theorem in those incoming manuscripts.
It identified a conservative gap that could be closed without weakening their
source-authentication requirements:

- `normal_cut_handlebodies._census` unconditionally refuses any annular
  attachment. The ordered source interface already provides enough information
  to distinguish saturated bases from harmless proper-boundary attachments.
- The marked-parallelity manuscript proves disk-interface gluing and saturated
  disc-base absorption. The new proper-boundary theorem applies to arbitrary
  unsaturated bases, including ones with full attached boundary circles.
- The interface-homology formula correctly eliminates every unsaturated base's
  boundary generators without adding a core relation. The relative one-handle
  theorem strengthens that algebraic observation to an actual geometric
  decomposition and a nonabelian free-product statement.
- The corner-aware kernel explicitly does not preserve arbitrary fundamental
  group words or lifted source paths. The new classifier retains that same
  limit: its genus summary is not a transported marking.
- Four-copy graph kernels address a different terminal graph predicate; their
  graph certificate is not an authentication of a ball or a bundle reduction.

The relevant claims are proved in the accompanying LaTeX section, including the
nonorientable-base case and a saturated Möbius-band counterexample with first
homology Z but nonabelian fundamental group. No general annular gluing rule is
inferred from an abstract homology presentation.

An independent read of `sector_extension/cluster_theorems.tex` found no logical
gap in the product factorization, anchored active-rank argument, exceptional
connected-support lemma, or candidate bit bound. The parent was advised to
spell out why a primitive extremal normal vector with Euler characteristic one
and nonzero boundary class is connected, and to cap the component enumeration
by `min(k,r)` when parameters can be binary encoded.
