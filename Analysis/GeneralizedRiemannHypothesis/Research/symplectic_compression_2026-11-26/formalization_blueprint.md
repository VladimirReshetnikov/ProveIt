# Formalization blueprint (not a compiled Lean development)

The new results in paper.tex have complete mathematical proofs and finite exact computational checks. No Lean proof or kernel-checking status is claimed for them. The upstream GRH development is a source of motivation, not a dependency needed by the theorem.

## Suggested dependency order

1. Fix a finite field k with cardinality q, finite-dimensional k-spaces, and an alternating bilinear form. In characteristic two retain `B v v = 0` explicitly; skew-symmetry alone is insufficient.
2. Define `PrescribedFrame H V` as an injective linear map whose pulled-back form is H. Prove its cardinality is E_n(d,s), by a symplectic decomposition plus an ordered isotropic frame count. Derive transitivity by completing an adapted basis. These are classical lemmas.
3. Prove a direct-sum graph lemma: an l-dimensional subspace in R0 ⊕ R1 ⊕ C, meeting both R0 and R1 trivially, is classified by (i) two k-subspaces, (ii) an isomorphism between them, (iii) an (l-k)-subspace of C, and (iv) a linear map into (R0 ⊕ R1)/graph. Use finite-cardinality equivalences, not numerical induction.
4. Deduce T_l and its positivity range l ≤ r - max(t0,t1). The maximal graph plus C gives the existence direction constructively.
5. Establish an equivalence between pairs of separately injective frames with fixed cross Gram matrix and the disjoint union, over allowed L ≤ radical Γ, of prescribed isometric injections of E/L. Include the identification ker(Y,X) ≅ im(Y) ∩ im(X).
6. Count this equivalence, divide by the frame cardinalities, and use orbit transitivity to turn uniform pairs into a fixed target and a uniform symplectic element. This proves the joint law.
7. Establish the support and minimal-dimension theorem by the positivity ranges; the construction in code/minimal_realization.py indicates explicit basis choices.
8. Separately formalize the rational function in z = q^(-2n). Its linear coefficient K is a finite algebraic computation. The asymptotic remainder can be handled through differentiability of a rational function with denominator nonzero at zero; only a finite family of matrices is involved.
9. Derive the scalar marginal by counting fibers of a nonzero linear functional on V minus {0}. Data processing for total variation then proves the nonzero leading coefficient.

## Principal statements

For two alternating spaces E1 and E0 and a cross-pairing A, put Γ = [[H1,A],[-Aᵀ,H0]], rank Γ = 2s, and ti = dim(rad Γ ∩ Ei). The central finite statement is:

    #(pairs of prescribed injective frames with cross Gram A and overlap l)
      = T_l(r,t0,t1) * E_n(a+b-l,s).

The realization statement, with no prior ambient space, is:

    (∃ separately injective realizations in a symplectic space of dimension 2n)
      ↔ s + max(t0,t1) ≤ n.

These statements should precede probability notation. All objects and sums are finite. The all-prime-power theorem must use genuine finite-field arithmetic, not integers modulo a composite q.

## Scope of the executable checks

The Python programs verify finite instances and output exact rational certificates. They do not replace the abstract proof and are not a verified implementation of a proof assistant. The field implementation covers prime fields and the explicitly represented field F4; the mathematics applies to all finite fields.
