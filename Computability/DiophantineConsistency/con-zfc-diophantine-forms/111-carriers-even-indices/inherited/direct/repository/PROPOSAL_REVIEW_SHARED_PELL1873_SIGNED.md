# Review of Shared Pell1873: signed indices and mixed domains

**PASS for the signed-index theorem and the emitted batching boundary.** The archive `ConZFC_Shared_Pell_1873.zip` is pinned by SHA256 `22147cf44bb6153b4f5097ba4bf4c81ba1973b7b77497fe95bd448b5f1bc8cee` (93 members,4,365,259 uncompressed bytes). All72 entries of its supplied SHA256 manifest verify; the companion receipt pins all93 arrival members. This is a scoped review, not a replay of the inherited logical calibration or a new Lean proof.

## Precise theorem and sign argument

Keep A,B,X,Y,U,k natural, with A,B≥2, X≥1, U≥2 and1≤k≤Y. Allow V,S,R to be arbitrary integers. Assume the three Pell norms, Y²∣V, and B≡A modU, B≡1 mod4Y, S≡X modU, R≡k mod4Y. Then X=X_k(A) and Y=Y_k(A). Nonzero V follows from U≥2, so the separate nonzero hypothesis is redundant. Positivity of the main coordinates and comparison base remains essential; the result does not allow arbitrary signed A,B,X,Y,U,k.

I checked the argument against the actual included Mathlib Pell source, whose Git blob is `db9c757dd7cac29260397150fd190d72715ea3f8` and SHA256 is `5c5756cdf2fa70fb77af9daa9c7167c65749ac616bde8f5fdfeed2cb958b3ed5`. The exact residue lemma accepts0<i≤n, including i=n. Classify the positive main pair at index i, the positive-absolute auxiliary pair at n, and the signed comparison pair as S=εX_h(B), R=δY_h(B), allowing independent signs. Square divisibility gives Y∣n and ordinate monotonicity gives i≤n. For ε=−1, shifting h to h+2n is indispensable: the half-period sign identity converts the signed abscissa residue to the positive one. The resulting residue classification gives h≡±i mod2n in both sign cases. The signed ordinate gives h≡δk mod4Y. Since Y∣n, combine these modulo2Y to obtain i≡±k. Finally1≤i,k≤Y resolves both signs, including the endpoint i=k=Y. There is no division by a possibly zero residue or unsupported coprimality assumption.

The proof includes Y=1, i=n and U=2. The h=0/R=0 branch contradicts R≡k mod4Y. V=0 contradicts U≥2. Merely taking absolute values of S and R and then applying the natural criterion would be invalid; the signed half-period argument supplies the missing step.

## Emitted graph and scoped checks

The actual batched graph retains natural predecessors enforcing X≥1,Y≥k,U≥2 and positive B. Its32 S/R progression quotients are explicitly unrestricted. The independent local auditor checks every required norm, progression, modulus, domain and call binding, all40 positive-power calls,19 exponent classes,16 seed tests,3 recurrence-derived pairs,192 exact identities and75 batch equalities. Its17 corruption controls reject altered norms/progressions/bounds/call coverage and recurrence data.

Fresh scratch runs of this auditor with negative controls pass in normal and `-O` modes with identical results. The separate signed verifier also passes both modes:18 parameter families,66 accepted congruence cases including all four sign combinations, and an exact wrong-index counterexample when Y²∣V is weakened. Those finite checks support the complete unbounded argument above; they are not its substitute. Historical natural-S/R review notes are explicitly superseded in the delivered archive.

## Compatibility with the projected667 source

The theorem is a sound route for deleting sign guards on its15 S and15 R progression quotients. It does not justify continuing to assert that all original667 coordinates are natural. For example, A=3,B=9,X=3,Y=1,U=3,V=1,k=1,S=−2889,R=−323 satisfies every displayed theorem hypothesis; its progression quotients are−964 and−81. This is an exact local certificate demonstrating the sign boundary, not a claimed full source zero.

The other22 prospective guard omissions need distinct arguments. For a power quotient h in `T*h=X−(A−n)Y−m`, positive main norm gives X>(A−1)Y. With n≥1 and T>m, the right side is greater than−m and hence greater than−T, so integer h≥0. For the common base quotient bq, the positive auxiliary norm with V≥1 gives U≥A; B>0 and B=A+U*bq exclude bq≤−1. These arguments must be applied after their main-coordinate bounds are established from the actual rows.

A complete improvement therefore needs a fresh sign/dataflow certificate excluding the signed private closure, a ledger binding every actual power argument and Pell test to the theorem, and an ordinary semantic proof. After signed-index recovery identifies all intended powers, fresh common positive comparison certificates can be constructed by the existing finite-unit/CRT completeness argument. This proves existential equivalence to the natural source without falsely proving pointwise positivity of the signed S/R values. No such new equation or reduced variable count is claimed by this review; it is a separate construction task.
