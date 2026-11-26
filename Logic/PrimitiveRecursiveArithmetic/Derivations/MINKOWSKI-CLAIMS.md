# Minkowski source-claim audit

This audit covers every theorem, lemma, proposition and corollary environment
in [`diophantine-number-theory/minkowski_ipra`](../docs/proofs/diophantine-number-theory/minkowski_ipra/).
There are six such environments. The certificate-form theorem and the
finite-prefix pigeonhole lemma are checked in full; the other four remain
unfinished. The checked enlargement dependency alone does not complete
the equality-case theorem. The delivered source is preserved; the full
repository scope is recorded in [PROGRESS.md](PROGRESS.md).

**Checked** below refers to ordinary `Prf PRAAx` derivations. Native Lean
lemmas, executable extraction and definitions of target propositions are
reported separately. A source theorem is complete only when its actual input
certificate/representation and its constructed output are connected by the
claimed object derivation.

## All six theorem environments

| Source claim | Checked scope and remaining work |
| --- | --- |
| `thm:main`, Certificate form of Minkowski, [01_foundations.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/01_foundations.tex), line 220 | **Checked complete original rational-box formula scheme.** [MinkowskiCertificate](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiCertificate.lean) `certificate_closed` proves correctness of the actual fixed PR2 extractor with internal dimension, box data and persistent formula parameter. The original [numerical checker](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiBoxChecker.lean) tests canonical list/box/rational endpoint codes, positive sides, literal separating axes and the actual rational content sum `W>1`; Boolean reflection is proved. [RationalBoxes](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiRationalBoxes.lean), [RationalContent](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiRationalContent.lean) and [ContentSum](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiContentSum.lean) construct the mesh and integer boxes and derive the exact product/sum count identity and threshold. The actual enumeration/residue extractor supplies a stored-length-correct integer vector and an actual nonzero coordinate. [Inside](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiInside.lean) derives each canonical half-center's original rational-box containment and obtains center membership from the original guarded `Inside` formula. [RationalNormalForm](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalNormalForm.lean), [WellFormed](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiWellFormed.lean) and the checked literal midpoint cancellation prove the canonical embedding and arbitrary-formula membership using the source's fully guarded symmetry/midpoint laws. No output point, collision, count threshold, containment or formula-value-extensionality conclusion is supplied. Membership is an arbitrary fixed formula; all numerical data remain internal. Source dimension positivity is retained. |
| `lem:php`, Bounded color collision, [02_finite_proof.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/02_finite_proof.tex), line 48 | **Checked actual finite-prefix search.** [MinkowskiPigeonhole](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiPigeonhole.lean) proves `bounded_color_collision` and `sequence_collision_closed` with actual PR pair-search metadata. Only `H≥1` and original colors below `H` at indices `i≤H` are required. Remainder totalization derives the global range used by [Core/Pigeonhole](Lean/IPRADerivations/Core/Pigeonhole.lean); returned bounds recover equality of original prefix colors. No supplied collision or stronger global range premise remains. |
| `lem:shrink`, Inner grid covers a shrink, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 91 | **Open.** Construct the actual floor-based cell and bounded containment checker. Retain certified `[-r,r]^n⊆P⊆[-R,R]^n`, `0<η<1`, `1/m≤ηr/2` and the computed search radius `T`. Derive that the chosen cell lies in the search window and passes every facet/vertex containment check. No supplied containment or successful-search conclusion may replace that proof. |
| `cor:poly`, Strict rational-polytope theorem, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 131 | **Open volume/geometry frontend.** Fixed-size determinant and adjugate identities exist, but the complete volume frontend and strict extractor do not. From the bounded symmetric rational body and rational matrix with nonzero determinant, construct normalization, inner/outer radii, certified volume lower bound and the explicit mesh; prove retained content exceeds one and invoke `thm:main`. Prove the actual nonzero-vector/lattice transport. |
| `thm:equality`, Integer-facet enlargement, [03_polytopes.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex), line 156 | **Checked dependency `eq:same-lattice`; complete theorem remains open.** [MinkowskiEnlargement](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiEnlargement.lean) supplies actual runtime dot sums, bound maximum and enlargement code `(M+2,M+1)`. `expanded_bound_gap`, `same_lattice_closed`, `same_lattice_program_closed` and `enlargement_metadata_closed` derive integer discreteness, membership equivalence and generated checker behavior. Public source guards include positive dimension/facet count/bounds and row/point shapes. Volume homogeneity, strict threshold growth, the rational enlarged-body presentation and the strict extractor remain. Boundedness and volume hypotheses belong to the unfinished complete theorem. |
| `prop:llpo`, Equality gives weak real sign choice, [04_represented_reals.tex](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/04_represented_reals.tex), line 99 | **Open source reduction.** [FiniteUseSignObstruction](Lean/IPRADerivations/Foundations/FiniteUseSignObstruction.lean) proves a related external exact-sign obstruction, not this weak-sign construction. Formalize the actual body `K_t`, positive reciprocal data from `1+t≥1/2`, sign extraction from a nonzero integer point, and the regular-name binary-sequence LLPO reduction. The packet leaves the stronger syntactic independence statement unimplemented; it must not be inferred from the semantic reduction. |

## Obligations outside theorem environments

The numerical specialization for rational bases and rational slab bodies
following `thm:main` is partially checked.
[RationalArithmetic](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalArithmetic.lean)
proves actual signed rational multiplication and min/max endpoint bounds.
[RationalFiniteSum](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalFiniteSum.lean)
constructs the canonical sums and derives their monotonicity from bounded
coordinate comparisons, with independently computed product denominators.
[RationalSumLinearity](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalSumLinearity.lean)
proves literal scalar homogeneity of the actual sum program, including zero,
negative scalars and empty sums.
[RationalSumAdditivity](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalSumAdditivity.lean)
`sum_additive_closed` proves literal additivity for the actual pointwise sum
of two independent input families. Its QF invariant retains all three raw
denominator products, with no supplied common scale or global sum equation.
[MinkowskiSlabInterval](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiSlabInterval.lean)
`dot_interval_closed`, `slab_checker_reflection_closed` and
`accepted_box_closed` prove the actual numerical min/max containment test:
acceptance by a fixed PR4 checker implies every point in the original
rational coordinate box satisfies every supplied row bound. The checker
uses actual endpoint products and sums; containment is derived, not supplied.
Dimension, facets, endpoints, coefficients and bounds are internal. The
arithmetic interprets total sequence coordinates in the first N positions;
stored-length or canonical shape guards are not silently inferred.

The supplied-row numerical slab theorem is now checked by
[MinkowskiSlabLinearity](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiSlabLinearity.lean)
and [MinkowskiSlabCertificate](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiSlabCertificate.lean).
Actual dot products commute with the actual vector negation and midpoint
programs as literal canonical scalar codes. The original slab inequalities
give the source's fully guarded symmetry and midpoint contracts.
An actual doubled-facet constructor feeds the interval test on every box;
`slab_inside_closed` derives the original doubled-coordinate `Inside`
contract. The fixed PR3 combined checker includes original numerical
`BoxOK` and these computed interval tests. `slab_certificate_closed` proves
that acceptance yields the original extractor's actual nonzero integer
vector and membership of its canonical embedding in every supplied slab.
`Inside`, symmetry, midpoint closure and output membership are conclusions,
not additional geometric premises. The scalar representation and affine
algebra used here are checked in
[RationalRepresentations](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalRepresentations.lean)
and [RationalAlgebra](Lean/IPRADerivations/Analysis/RationalArithmetic/RationalAlgebra.lean).

The physical-basis specialization remains open: construct `aB` from the
physical rows and rational basis, prove the dot-product transport identifying
this numerical slab body with `Bq∈K`, and construct/check the physical
nonzero lattice output `Bz`, uniformly in dimension. The supplied-row
theorem does not assume or implement those matrix and injectivity proofs.

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

## Complete rational certificate construction

The pure signed mesh kernel from
[Section 2](../docs/proofs/diophantine-number-theory/minkowski_ipra/paper/02_finite_proof.tex)
is checked independently of the unfinished volume frontend:

1. **Checked:** [SignedEuclidean](Lean/IPRADerivations/DiophantineNumberTheory/SignedEuclidean.lean) constructs actual signed quotient/remainder and proves `a=mq+r`, `r<m`,
   including negative coordinates and `m=1`; actual PR output metadata and equal-residue/nonzero-difference transport are checked.
2. **Checked:** [MinkowskiResidues](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiResidues.lean) constructs the runtime-dimensional reverse Horner residue-color fold. Range below `m^n`, actual quotient/remainder peeling, coordinate residue injectivity and the exact signed difference equations are derived; `n=0` and `m=1` are included.
3. **Checked:** [MinkowskiMesh](Lean/IPRADerivations/DiophantineNumberTheory/MinkowskiMesh.lean) applies the actual pigeonhole witnesses to a supplied list with at least `m^n+1` entries. The premise concerns decoded integer-vector distinctness, not different raw codes for one vector.
4. **Checked:** its actual PR3 returned fields include the quotient vector `z` and the least searched nonzero coordinate. `mesh_correct_closed` derives every equation `a−b=mz`, the exact output vector length and a decoded nonzero entry from the supplied prefix guard; no collision or output nonzero premise is used.

The original rational certificate now feeds this mesh kernel through actual
programs. The complete endpoint pool contains every lower and upper row;
its product denominator is the mesh. Original rational comparisons derive
integer sides and separation. QF product induction proves each actual box
count identity; the actual rational-sum recursion and a second QF induction
prove `contentDen*actualCount=mesh^n*contentNum`. Positive mesh and
`contentNum>contentDen` yield the required count threshold. No desired global
identity or count inequality is an input.

The original numerical `BoxOK` is a fixed PR2 Boolean checker. Its bounded
syntax includes canonical outer sequences, literal paired boxes, canonical
rational endpoint vectors, sides, separating axes and the actual rational
content threshold. Its reflected source formula is used in the complete
certificate theorem. Malformed inputs are totalized by the decoders and
receive no correctness promise without checker acceptance.

The actual gcd normalizer now has proved coprimality, disjoint signed parts,
literal reduced-code uniqueness, zero denominator one and idempotence.
Generated rational vectors have their actual length, canonical sequence
reconstruction and reduced entries. The canonical half-cell center has
proved original rational endpoint bounds. Actual normalized doubling
returns its literal doubled-center vector code, so the source's guarded
`Inside` formula supplies the two center memberships. Literal midpoint
cancellation and the fully canonical guarded symmetry/midpoint laws then
supply membership of the canonical integer embedding. Arbitrary membership
formulas retain their internal numerical parameters; no induction on them
or rational-value-extensionality assumption is used.

`MinkowskiCertificate.certificate_closed` is the complete source uniform
extractor scheme. `solution_programs_closed` identifies its fixed PR2 trace,
integer-vector and nonzero-coordinate programs. The output includes the
actual coordinate bound and decoded nonzeroness, vector length, canonical
rational embedding guard and formula membership. `certificate_exists_closed`
also gives the corresponding existential formulation. The rational-polytope,
enlargement/volume and represented-real source claims remain separate, as
recorded in the four unfinished rows above.
