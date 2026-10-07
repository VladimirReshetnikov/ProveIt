# Formalization plan

This is a dependency blueprint, not checked Lean source. No new formalization count should be inferred from its presence.

## Recommended first target

Formalize the finite theorem for explicit parameters r, T and a prime p exceeding the displayed threshold. Keep the asymptotic extremal constants out of the first pass. All parameter computations and arc endpoints are rational; the limiting statement can be added later.

## Proposed dependency order

### 1. Finite cycle boundary

For a finite cyclic group and a nonempty proper subset represented by M disjoint cyclic intervals separated by nonempty gaps, prove that the number of exits under addition by one is M. Prove separately that `|B \ (B+d)|` equals the exit count `{x in B : x+d notin B}` and that the symmetric-difference cardinality is twice either one-sided count.

### 2. Rational arc grid counts

Represent a short rational circle arc by a lifted real/rational interval of length below one. Show injectivity of integer points modulo p and the exact cardinality formula `floor(p*right) - ceil(p*left) + 1` when nonempty. Prove discrepancy at most one, including the zero-crossing arc. Establish sufficient positive-length/gap hypotheses for the finite cycle theorem.

### 3. CRT parameters

Define s=r-1, D=s!, q_i=T+iD, A=product q_i. Prove pairwise coprimality from `T mod D = 1 mod D`. Show all A/q_i are integers and that the defining frequencies are positive and distinct. Produce CRT witnesses x_S and prove the zero, negative and reflected positive residue patterns are distinct.

### 4. Modular-to-linear classification

Use the a_0 constraint to obtain the unique x,u representation. Derive the residual identity. Bound the centered residue by a real number below two, hence restrict it to -1, 0, 1. Prove an unwrapping lemma under an absolute value below one-half and rule out mixed signs. Identify the exact interval for each allowed subset S; no separate existence assumptions about components are permitted.

### 5. Endpoints, lengths and mass

Prove monotonicity of L_i and U_i, the minimum positive length and the gap bound. Prove the subset-minimum counting identity `#{S : min S = i}=2^(s-i)`. Derive the exact mass sum. In a purely finite first pass, the mass can be represented by the sum of rational interval lengths rather than Haar measure.

### 6. Finite prime theorem and deletion witnesses

Combine steps 1–5 with p > 8 A T^2. Prime order is not needed for the counting lemmas; it is an extra ambient-group property in the final theorem. For essentiality, formalize the strict witness when deleting each a_i and the separate strict witness when deleting a_0. An explicit rational margin can give an effective grid cutoff rather than an abstract density argument.

### 7. Probability interface

Prove the total-variation identity for uniform finite-set measures. The approximation/translation tradeoff then follows from the triangle inequality and invariance under translation. These lemmas are independent of Bohr sets and should be placed in a reusable namespace.

### 8. Limits and extremal constants

For fixed r and T, derive the prime-grid ratio limit from the discrepancy estimate. Let T run through an arithmetic progression to obtain M/2. Formalize a uniform small-step threshold in the smoothing rule so that the limiting argument cannot accidentally permit a separate vacuous threshold for each finite instance. Only then introduce the suprema defining c_r.

## Reuse and attribution

The main construction needs no theorem from the unverified all-length progression manuscript. Existing ProveIt Bohr definitions may be reused after reconciling absolute angular step with the article's relative step. The earlier escape-tube upper lemma is an imported/attributed result, not part of the new contribution count. The source audit names the existing parameter-normalization correction.

## Certificate checker opportunity

A reusable checker could consume integer parameters, CRT witnesses and rational interval certificates. It should verify both coverage (all original constraints imply one listed interval) and soundness (every listed interval satisfies all constraints), not just endpoint samples. The delivered Python code checks finite examples and rational identities; it is not yet this kernel-verified checker.
