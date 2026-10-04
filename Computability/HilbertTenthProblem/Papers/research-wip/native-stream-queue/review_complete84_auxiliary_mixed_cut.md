# Independent review: mixed arithmetic at the auxiliary cut

**PASS with the stated protected-row restriction.** Joint production of V=cTf-c-Rf² and W=Delta*f² needs at least seven gates from the six independent cut variables and the dependent paid monomials c²,Delta*c². Keeping the two actual coefficient rows and final S=W-Q subtraction therefore forces at least ten gates. A separate argument forces at least three additions for unrestricted joint V,Q,S production. Neither conclusion proves a global lower bound for the complete universal polynomial or a ten-gate bound when all coefficient/strong rows may be changed.

## Read scope and pins

The reviewer read the entire fresh helper and proof, inspected the complete saved source relation, and checked the mathematical arguments below. The author artifacts are:

| Artifact | SHA-256 |
|---|---|
| complete84_auxiliary_mixed_cut.py | a77f326d98550ed21643d5f1ea2aa25d9dca7d9a7fdca26c40e8bf1cdf80c13a |
| complete84_auxiliary_mixed_cut.json | 1aa60da5b6b7278efdfd8535d10ec8f9af604b729b1f95c124eca714721dfc47 |
| complete84_auxiliary_mixed_cut.md | b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2 |

The helper checks six predecessor byte pins. Predecessor programs were not executed or imported. Fresh normal and optimized type-exact receipt replays from `/` both pass.

## Multiplication and addition arguments

After Delta=i=0, original paid expressions have degree at most two and the only quadratic one is c². If the first useful product has degree at least three, multiplying an expression that genuinely uses it by a nonconstant expression creates a higher leading degree that the output cannot cancel using the earlier span. If the two useful products are independent, all their cubic terms are divisible by c², including after cancellation of quartic terms. They cannot give f(cT-Rf).

If the first useful product has degree two, its leading part is a product of linear forms. A second product producing a cubic without an uncancellable quartic must have cubic leader L(alpha*c²+beta*l1*l2). The irreducible quadratic cT-Rf forces L to be proportional to f. The remaining quadratic cT-Rf-lambda*c² has Hessian determinant1 for every lambda, so cannot be a product of linear forms. This proves the three-product bound for V even with arbitrary free linear combinations.

For the pair V,W, W is not in the original paid span. In its linear representation by paid ports and product outputs, specialize Delta=i=0 and eliminate the greatest-index product with a nonzero coefficient. This leaves a circuit for V with one fewer multiplication. The elimination uses only free linear operations within this multiplication-only argument. Hence the pair needs at least four products.

For a circuit with two additions, irreducibility forces V to be the second addition itself up to a nonzero scalar. The first addition is a binomial g; the output must be a monomial times a power of g plus one monomial. A power at least two cannot yield V's three noncollinear support points. Thus the first binomial groups two terms of V. Their possible common monomial factors are exactly c,f,1. The three cases in the author's table are exhaustive, including the cases where no factor is extracted. W cannot be produced from either nonmonomial addition by multiplication. Its cone is monomial. The target divisors then give at least five products in every case; only a newly produced f² can be shared in the first two cases. This closes the possible four-product/two-addition six-gate case and proves seven gates.

For the protected ten-gate result, specialize i=0 and delete U=i*Ac2, Q=U², and S=W-Q. Any downstream use of U or Q becomes zero and any downstream use of S becomes W, so chronological interleaving does not defeat the deletion. The remaining graph must produce V,W and needs at least seven gates. The proof requires those three literal rows and the declared paid cut; it makes no assumption that every other row remains in its original order.

The unrestricted three-addition proof is also valid. V and P=f²-Delta*i²*c⁴ are primitive irreducible polynomials with distinct factors. With only two additions, V must first occur at the second, and S=Delta*P must arise multiplicatively from the first binomial. Multiplicity forces that binomial to be a monomial times P. Modulo P, localizing c and i sends Delta to f²/(i²*c⁴), so V would have to become a Laurent monomial. Its three terms remain distinct by T and R, a contradiction. Supplying every monomial free only strengthens the allowed model; no Laurent monomial is supplied to the original circuit.

## Source and supplementary verification

The new attaining schedule replaces only the five private quotient rows following f². A separate exponent-dictionary expansion independently confirms c(Tf-1)-Rf²=f(cT-Rf)-c. The unchanged three external cuts feed identical downstream expressions. The helper verifies all84 gates and25 supplied ports are live, counts47M+37A, and proves the full polynomial identity. Thus the18 positive witnesses and uniform exact degree187 are inherited without a new degree calculation or compiler-zero assumption.

An independent inline interpreter performs64 complete signed modular comparisons over two primes. Every unchanged row, the proved V cut and the full output agree. These checks supplement the exact cut proof and full literal downstream reconstruction; they are not positive native witness fixtures. The author's twelve signed integer evaluations have the same limited role.

The four-product, two-addition and three-addition lower bounds are mathematical claims established by the symbolic arguments, not inferred from finite enumeration. The exact Hessian and support certificates in the receipt check their algebraic ingredients. The resulting nine-gate search restriction is useful but local: any such improvement must have at most six multiplications and change at least one of the protected rows. The established universal84 frontier remains unchanged.

A second independent mathematical challenge read the entire frozen proof and checked all of the multiplication, specialization, two-addition classification and unrestricted three-addition arguments. It found no defect and explicitly confirmed the S-to-W substitution for later consumers. This was a proof review, not an additional executable test.
