# Contribution and source audit

Source snapshot: `b0f6f535ffc16324683fef2c263260a88ae03755` of VladimirReshetnikov/ProveIt.

## Main contribution

The previously delivered finite multiplication/spanning certificate contains enough information for a complete rational-point list, rather than merely the known cardinality bound. Clear each multiplication matrix's rational denominators. A rational evaluation row vector is an eigenvector. Scale the row to a primitive integer vector; its eigenvalue has denominator one by a coordinate divisibility/Bezout argument. Its absolute value is bounded by the maximum absolute column sum of the integer matrix. Thus every rational coordinate lies on an explicit finite rational grid, and filtering that grid is complete.

The primitive-vector proof avoids Cayley-Hamilton, determinants, rational algebraic integers, matrix commutativity and basis independence. The observable-module statement applies to specified PR rational observables of arbitrary coded objects; complete enumeration follows only with coordinate reconstruction. This last distinction prevents overclaiming.

## Direct predecessor

`Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_embedding_framework/paper/05_diophantine.tex`, subsection “Finite algebra certificates as a general zero-count interface”, lines 236 onward.

It defines `b_1=1`, rational multiplication matrices and exact polynomial residual witnesses. It proves that any finite list of rational zeros has length at most D using interpolating polynomials and row reduction. It does not extract coordinate denominator/height bounds or enumerate a complete zero set. The present result should explicitly credit that certificate definition and cardinality theorem.

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/b0f6f535ffc16324683fef2c263260a88ae03755/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_embedding_framework/paper/05_diophantine.tex

## Related pre-existing algebra

`Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/cayley_hamilton_ipra/sections/applications.tex`, section “Finitely generated modules and integral elements”, subsection “The determinant trick without a basis”, beginning at line 192.

It proves the classical finite-generator Cayley-Hamilton/determinant trick, without linear independence; later it proves finite integrality constructions. This explains a conventional alternative route to our integer-eigenvalue lemma. We do not claim historical originality for rational eigenvalue integrality, finite algebra enumeration, or the determinant trick. The novelty is a specific strengthened, lightweight interface within the reviewed repository and its detailed iPRA compilation plan.

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/b0f6f535ffc16324683fef2c263260a88ae03755/Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/cayley_hamilton_ipra/sections/applications.tex

## Latest framework context

The following README files were read through GitHub at the pinned snapshot:

- `docs/proofs/foundations/ipra_finite_demand/README.md`
- `docs/proofs/foundations/ipra_coherent_methods_2026-11-15/README.md`
- `docs/proofs/foundations/ipra_uniform_certificates/README.md`
- `docs/proofs/foundations/ipra_evidence_framework/README.md`
- `docs/proofs/README.md`

They already supply finite observation/certificate infrastructure, filtered lifting, weighted polynomial norms, root supports, relational witnesses, and bounded search/finite-list mechanisms. Those ingredients must be credited rather than reintroduced as new.

## Exact worked example

F1 = 4 y² − 4 x³ + x − 4; F2 = 2 x² − x.
b=(1,x,y,xy); c=(1,0,0,0).

Matrix convention: v=(b_i(p)) is a row and v M_k = p_k v.

Mx rows:
  (0,0,0,0)
  (1,1/2,0,0)
  (0,0,0,0)
  (0,0,1,1/2)

My rows:
  (0,0,1,0)
  (0,0,0,1)
  (1,0,0,0)
  (0,1,0,0)

Δx=2, Δy=1; maximum absolute column sums R=(2,1).
The resulting grid has 5×3=15 candidates.
Its exact filtered list is (0,±1),(1/2,±1).

Nonzero residuals:

- x*b2 − b2/2 = F2/2.
- x*b4 − b4/2 = y F2/2.
- y*b3 − b1 = [F1+(2x+1)F2]/4.
- y*b4 − b2 = x[F1+(2x+1)F2]/4.

## Noncommuting redundancy test

For F=(x,y), b=(1,0,0), c=(1,0,0), choose matrices with first row and column zero and lower-right blocks

Mx: [[0,1],[0,0]], My: [[0,0],[1,0]].

They do not commute. The only nonzero residuals are x*b1=x=F1 and y*b1=y=F2. The certificate is valid, and enumeration gives only (0,0). A checker that insists on commutation would reject useful redundant presentations unnecessarily.

## Scope limitations

No uniform certificate constructor for arbitrary equations is claimed. No complete point list for an arbitrary positive-dimensional curve follows. No general Siegel/Faltings/Mordell-Weil result follows. A finite cardinality bound on a decidable set remains insufficient for a search bound; the matrix-action certificate is a much stronger structural input.

The general observable statement is schematic in fixed PR evaluators with proved local contracts. The polynomial specialization is uniform in finite polynomial codes because that grammar has one fixed PR evaluator. Neither interpretation assumes a total universal evaluator for arbitrary primitive-recursive programs.
