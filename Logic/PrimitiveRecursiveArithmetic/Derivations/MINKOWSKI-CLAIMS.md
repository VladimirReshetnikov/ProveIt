# Minkowski source-claim audit

This audit covers every theorem, lemma, proposition and corollary environment
in [`diophantine-number-theory/minkowski_ipra`](../docs/proofs/diophantine-number-theory/minkowski_ipra/).
There are six such environments. The finite-prefix pigeonhole lemma is
checked in full; the other five remain unfinished. The checked enlargement
dependency alone does not complete the equality-case theorem. The delivered source is preserved; the full
repository scope is recorded in [PROGRESS.md](PROGRESS.md).

**Checked** below refers to ordinary `Prf PRAAx` derivations. Native Lean
lemmas, executable extraction and definitions of target propositions are
reported separately. A source theorem is complete only when its actual input
certificate/representation and its constructed output are connected by the
claimed object derivation.

## All six theorem environments

| Source claim | Checked scope and remaining work |
| --- | --- |
| `thm:main`, Certificate form of Minkowski, [01_foundations.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/01_foundations.tex), line 220 | **Partial: pure mesh kernel checked; assembled geometric extractor open.** [MinkowskiMesh](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiMesh.lean) constructs actual PR3 selected indices, quotient-difference vector and least nonzero coordinate from a sufficiently long decoded-distinct cell list. It proves index/output lengths, every exact scaled difference and actual integer nonzeroness. The remaining `BoxOK` producer must construct that list and derive its guards from nonempty boxes, positive sides, disjoint interiors and content greater than one. Then prove canonical rational cell-center cancellation and instantiate `InsideΦ`, symmetry and midpoint. Arbitrary-formula `Φ` needs canonical rational codes or a proved rational-extensionality contract; equal values of unreduced fractions do not permit substituting arbitrary raw codes. |
| `lem:php`, Bounded color collision, [02_finite_proof.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/02_finite_proof.tex), line 48 | **Checked actual finite-prefix search.** [MinkowskiPigeonhole](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiPigeonhole.lean) proves `bounded_color_collision` and `sequence_collision_closed` with actual PR pair-search metadata. Only `H≥1` and original colors below `H` at indices `i≤H` are required. Remainder totalization derives the global range used by [Core/Pigeonhole](Lean/IPRADerivations/Core/Pigeonhole.lean); returned bounds recover equality of original prefix colors. No supplied collision or stronger global range premise remains. |
| `lem:shrink`, Inner grid covers a shrink, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 91 | **Open.** Construct the actual floor-based cell and bounded containment checker. Retain certified `[-r,r]^n⊆P⊆[-R,R]^n`, `0<η<1`, `1/m≤ηr/2` and the computed search radius `T`. Derive that the chosen cell lies in the search window and passes every facet/vertex containment check. No supplied containment or successful-search conclusion may replace that proof. |
| `cor:poly`, Strict rational-polytope theorem, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 131 | **Open volume/geometry frontend.** Fixed-size determinant and adjugate identities exist, but the complete volume frontend and strict extractor do not. From the bounded symmetric rational body and rational matrix with nonzero determinant, construct normalization, inner/outer radii, certified volume lower bound and the explicit mesh; prove retained content exceeds one and invoke `thm:main`. Prove the actual nonzero-vector/lattice transport. |
| `thm:equality`, Integer-facet enlargement, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 156 | **Checked dependency `eq:same-lattice`; complete theorem remains open.** [MinkowskiEnlargement](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiEnlargement.lean) supplies actual runtime dot sums, bound maximum and enlargement code `(M+2,M+1)`. `expanded_bound_gap`, `same_lattice_closed`, `same_lattice_program_closed` and `enlargement_metadata_closed` derive integer discreteness, membership equivalence and generated checker behavior. Public source guards include positive dimension/facet count/bounds and row/point shapes. Volume homogeneity, strict threshold growth, the rational enlarged-body presentation and the strict extractor remain. Boundedness and volume hypotheses belong to the unfinished complete theorem. |
| `prop:llpo`, Equality gives weak real sign choice, [04_represented_reals.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/04_represented_reals.tex), line 99 | **Open source reduction.** [FiniteUseSignObstruction](Lean/IPRADerivations/Foundations/FiniteUseSignObstruction.lean) proves a related external exact-sign obstruction, not this weak-sign construction. Formalize the actual body `K_t`, positive reciprocal data from `1+t≥1/2`, sign extraction from a nonzero integer point, and the regular-name binary-sequence LLPO reduction. The packet leaves the stronger syntactic independence statement unimplemented; it must not be inferred from the semantic reduction. |

## Obligations outside theorem environments

The [finite-volume appendix](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/06_finite_volume.tex)
has no theorem-style environment. It still supplies essential requirements:

- Bounded vertex enumeration and actual convex-combination construction.
- Compatible barycentric triangulation and determinant boundary cancellation.
- Refinement-independent rational content and finite additivity.
- Covering monotonicity and affine determinant scaling.
- Cube/box content formulas with the exact supplied certificate conventions.

[Algebra/CayleyHamilton](Lean/IPRADerivations/Algebra/CayleyHamilton.lean)
`det_mul` and [AdjugateInverse](Lean/IPRADerivations/Algebra/AdjugateInverse.lean)
`mul_adj`/`adj_mul` are fixed-size object identities. They do not implement
runtime-dimensional volume, row selection, geometric coverage, or certificate
construction.

## Delivered evidence and its limits

The archived [FiniteKernel.lean](../docs/proofs/diophantine-number-theory/minkowski_ipra/lean/FiniteKernel.lean)
contains executable native definitions and lists proof obligations; it has no
complete kernel-correctness theorem.
[GeometricBridge.lean](../docs/proofs/diophantine-number-theory/minkowski_ipra/lean/GeometricBridge.lean)
contains native rational `difference_mem` and `injective_map_nonzero` results;
the centered-mesh identity remains an obligation.
[ObjectTarget.lean](../docs/proofs/diophantine-number-theory/minkowski_ipra/lean/ObjectTarget.lean)
defines the desired correctness formula and conditional interpretation
transport. Its concrete arithmetic symbols and correctness derivation still
need construction.

Python extraction, independent witness checking and the archive's nine tests
are executable evidence. They do not establish all-input ordinary iPRA
correctness. The source labels its Lean outlines uncompiled; this audit does
not revise those historical artifact claims into object-theory proof claims.

## Pure mesh extraction checked; box refinement and geometric transport remain

The pure signed mesh kernel from
[Section 2](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/02_finite_proof.tex)
is checked independently of the unfinished volume frontend:

1. **Checked:** [SignedEuclidean](Lean/IPRADerivations/DiophantineNumberTheory/SignedEuclidean.lean) constructs actual signed quotient/remainder and proves `a=mq+r`, `r<m`,
   including negative coordinates and `m=1`; actual PR output metadata and equal-residue/nonzero-difference transport are checked.
2. **Checked:** [MinkowskiResidues](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiResidues.lean) constructs the runtime-dimensional reverse Horner residue-color fold. Range below `m^n`, actual quotient/remainder peeling, coordinate residue injectivity and the exact signed difference equations are derived; `n=0` and `m=1` are included.
3. **Checked:** [MinkowskiMesh](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiMesh.lean) applies the actual pigeonhole witnesses to a supplied list with at least `m^n+1` entries. The premise concerns decoded integer-vector distinctness, not different raw codes for one vector.
4. **Checked:** its actual PR3 returned fields include the quotient vector `z` and the least searched nonzero coordinate. `mesh_correct_closed` derives every equation `a−b=mz`, the exact output vector length and a decoded nonzero entry from the supplied prefix guard; no collision or output nonzero premise is used.

The checked `mesh_correct_closed` has exactly the pure-kernel form
`MeshGuard → correct(N,m,L,meshF(N,m,L))`, with dimension, modulus,
list lengths and coordinates internal. Source vectors use total signed
coordinate decoders; there is no asserted zero padding of malformed vectors.
The geometric producer can require each stored vector length to equal `N`. The subsequent box-refinement proof
must derive `MeshGuard` from the original `BoxOK` certificate. It must not
silently replace the original certificate by an assumed mesh-extraction
conclusion.
