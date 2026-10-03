# Independent adversarial review

Date: 2026-10-03

## Result

No mathematical soundness, numerical generator, orientation, or census error was found in the reviewed compiler, numerical packet, and test code. The general marker argument below rules out arbitrary spurious semigroup products; the accompanying finite computations are additional consistency checks, not a substitute for that argument.

The separate source-universality audit is a dependency, not something this review re-proves. In particular, the mathematical many-one completeness conclusion may use the cited effective Neary–Woods simulation, while the released executable starts with finite U15 tape halves. It must not be described as an implemented arbitrary-program loader.

## 1. Independent numerical checks

`independent_check.py` imports only Python's standard library and reads the newly authored JSON packet and accepting witness. It imports neither the compiler nor any upstream repository code.

It verifies:

- Exactly 229 distinct block-diagonal integer generators, each with determinant one
- Every upper and lower block against the stated formula, with E_j recomputed by literal shear conjugation
- 20 rewriting letters, the full 93-rule inventory reconstructed independently from the pinned transition data, and all 114 correctly oriented nonerasing tiles
- Maximum absolute entry 63,038,000; 1,831 nonzero entries; aggregate magnitude bit length 21,372
- The literal correspondence equality for the saved accepting witness
- An independently extracted 14-step serial rewriting derivation, by applying disjoint block rewrites right to left
- Literal evaluation of the 189-generator product against the full 4-by-4 target
- All 960,800 words through length seven over A_1,A_57,A_114,B_1,B_57,B_114,C, comparing exact numerical matrix equality, abstract free-group reduction, and the asserted marker language. Exactly 40 words accept; all have the expected form

The packet hash and replay results are in `independent-results.json`. These bounded tests make no nonhalting claim.

## 2. Freeness is sufficient in SL2(Z), not just projectively

Let P(z)=z+2 and Q(z)=z/(2z+1) on the real projective line. For nonzero integers n, P^n sends the set |z|<1 into |z|>1, and Q^n sends |z|>1 into |z|<1. Standard ping-pong, or cyclic reduction followed by these strict inclusions, shows that P,Q generate a free group. The proof distinguishes a nontrivial word from the identity even in the projective action, so an accidental scalar matrix does not invalidate the claim in SL2(Z).

For E_j=Q^(-j) P Q^j, a nonempty reduced word in distinct E_j generators can be grouped as E_{j1}^{n1} ... E_{jr}^{nr}, with nonzero n_k and distinct adjacent j_k. Its expansion contains nonzero P powers separated by the nonzero Q powers Q^{j_k-j_{k+1}}. It cannot freely reduce to the identity. This proves the free independence of the E_j used in both blocks, including E_0=P for the marker block.

## 3. Exact marker language: proof for arbitrary product length

Write t=E_0 and x_i=E_i, 1<=i<=114. These are a free basis of the subgroup they generate. The bottom factors are

- A_i: x_i
- B_i: t^(-1) x_i^(-1) t
- C: t

The exponent homomorphism sends t to 1 and every x_i to 0. This is an exponent in this free basis; it is not the P-exponent in the ambient basis P,Q. Each C contributes one and every A_i,B_i contributes zero. A product equal to t therefore contains exactly one C.

The kernel of that exponent homomorphism has free basis y_{i,h}=t^h x_i t^(-h), for i in 1,...,114 and integers h. Push the residual t to the right. Before C, an A_i contributes y_{i,0} and a B_i contributes y_{i,-1}^(-1). After C, an A_i contributes y_{i,1} and a B_i contributes y_{i,0}^(-1).

No positive y_{i,-1} occurs anywhere. Thus any B before C leaves a letter that cannot be erased in free reduction. No negative y_{i,1} occurs anywhere. Thus any A after C likewise cannot be erased. Consequently a word equal to t must consist entirely of A letters before C and B letters after C. The remaining kernel word is a positive word in y_{i,0} followed by a negative word, so it is trivial exactly when the B indices reverse the A indices. Conversely every such product has bottom block t by direct cancellation.

This includes the case C alone. There are no additional products caused by inserting identities, since the same argument excludes every unwanted positive generator string.

## 4. Top-block orientation

For a tile sequence s=(i1,...,ik), the forced generator word is

    A_i1 ... A_ik C B_ik ... B_i1.

Its upper block is

    Phi(h(s)) Phi(X#)^(-1) Phi(g(s))^(-1).

It equals Phi(w#)^(-1) precisely when

    Phi(w# h(s)) = Phi(g(s) X#).

Since the top alphabet is sent to a freely independent set, its positive-word encoding is injective. Thus matrix equality is equivalent to the literal word equality

    w# h(s) = g(s) X#.

Both reversal in the B sequence and inversion of the whole g(s) word are essential. They are correctly implemented.

## 5. Separator edge cases and directed derivation

Each nonseparator tile has nonempty h and g and contains no #. Let k be the number of separator tiles, and split s into k+1 nonseparator blocks. The final block must be empty because the right side of the correspondence equation ends with # and the h-image of every nonseparator tile is nonempty.

If k=0, the sequence is empty and the equation says w=X. If k>0, comparison of # separated blocks says that the first g-block is w, each h-block equals the next g-block, and the final nonempty-position h-block is X. A block may itself contain no tiles only when both its words are empty; this does not introduce spurious rewrites.

Inside each block, copy tiles preserve letters and rewrite tiles replace disjoint source occurrences u by their directed outputs v. These occurrences can be serialized from right to left without offset adjustment. Therefore every equality yields w ->* X. Conversely, each individual rewrite with copied context followed by a separator gives a block, and concatenating those blocks gives the correspondence equality. Direction is preserved; no reverse rule is used.

## 6. Machine simulation and scope

Every legal configuration has exactly one state symbol before its scanned bit. The transition rules inspect the neighboring bit, or extend the finite window with a blank at the indicated boundary. There is exactly one applicable transition/halt rule until J1 is reached. Only the J1 rule creates X. Once X is created, the two-sided bit erasures followed by [X] -> X finish; they cannot create a halt before J1 occurs. This establishes the local finite-tape equivalence for every finite binary initialization, including differently padded spellings of the same infinite blank-tailed tape.

The encoder's O(n) matrix multiplication count and linear output magnitude-bit bound are correct for a given finite tape of length n. They do not imply a polynomial-time arbitrary-program-to-target compiler without an additional input-compilation bound.

## Written proof review

Reviewed the actual ten-section `PROOF.md` at 16:14 UTC. Its separator decomposition, arbitrary-length marker proof, upper-block multiplication order, nonempty-semigroup convention, and separation of executable versus published universality claims are sound.

The O(n^2) finite-tape bit bound in Section 9 is valid: the kth multiplication involves O(k)-bit entries and fixed-size integer factors, costing O(k) with elementary arithmetic. Summing gives O(n^2). The implemented `inv()` also computes a determinant using two variable-size integer multiplications. Even under a schoolbook arithmetic bound this is O(n^2), so the claimed total upper bound survives. The stored matrices and elementary arithmetic can use O(n) working bits.

One minor resource-description correction was sent to the author: the two-by-two inverse formula swaps the two diagonal entries once and changes two signs; it does not require two swaps. If the operation description is intended to track the executable exactly, it should also mention the determinant-validation products. Neither point changes the theorem, numerical packet, or asymptotic bound.

### Verified resolution

At 16:18 UTC on 2026-10-03, independently re-read Section 9 and confirmed both wording corrections: one diagonal-entry swap and two sign changes, plus the implemented determinant check using two variable-integer multiplications and a subtraction. The minor review finding is resolved. The semigroup JSON SHA-256 remains `506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9`, so the audited numerical packet is unchanged.

### Final bibliographic correction and reviewed artifact binding

At 16:22 UTC on 2026-10-03, confirmed that Section 8, `PROVENANCE.json`, and the loader dependency audit consistently distinguish the published record from the author/draft PDF's printed-page locators. Independently opened the [publisher record](https://journals.sagepub.com/doi/10.3233/FI-2009-0036), which confirms *Fundamenta Informaticae* 91(1) (2009), pages 123–144, DOI 10.3233/FI-2009-0036. The local documentation explicitly marks pages 105–126, including Table 16 on printed page 121, as author/draft-PDF pagination. This bibliographic correction does not change the reviewed mathematical argument or the numerical data. The stated distribution policy excludes the primary-PDF reading cache; this note does not certify the future ZIP contents.

The unchanged mathematical review above applies to these final file hashes:

- `PROOF.md`: SHA-256 `8764c608e380132e6e226c7e2f7754bf591579bdbea1162511179677a0663794`
- `data/semigroup.json`: SHA-256 `506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9`
