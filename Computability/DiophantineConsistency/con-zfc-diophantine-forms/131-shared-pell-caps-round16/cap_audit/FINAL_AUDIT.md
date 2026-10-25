# Independent audit of the final signed Pell cap equations

## Verdict

No mathematical defect was found in the final signed construction or its two compiled endpoints. The exact audit independently reconstructs the complete changed source, guards, factorization, projection, translations and collected quartic. The written unbounded argument was reviewed separately, including every sign and zero-index branch, the anchor's comparison center of either sign, the cofinal beta restriction, and the self-sized radix.

The two checked ordinary integer polynomials are:

- `../direct/integer324/equation.json`: 324 unrestricted integer variables, 208 quadratic residuals, degree four, 5,808 collected monomials, coefficient height 128,446.
- `../direct/integer338/equation.json`: 338 unrestricted integer variables, 222 quadratic residuals, degree four, 4,493 collected monomials, coefficient height 128,446.

Their nonzero coefficients are in the adjacent `expanded_polynomial.json` files. They are distinct Pareto alternatives, not a claim of global minimality. The exact endpoint hashes are in `FINAL_ENDPOINT_CHECK.json`.

The arithmetic and inherited logical calibration together identify zero-existence with a finite syntactic ZFC refutation. This audit does not decide zero-existence, prove consistency, or emit a new end-to-end Lean, Rocq or object-language ZFC proof. The retained calibration interfaces are `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

## What is new and what remains inherited

The incoming Shared Pell Bound 261 construction supplies the unsigned pooled-cap idea. The initial signed two-coordinate version is checked in `SIGNED_CAP_AUDIT.md`. The final released form uses only squared ordinate errors, recovers abscissa signs from ordinary power requests, and adds a stronger aggregate that simultaneously supplies the anchor's lower bound. The square-output factorial/product fusion, local arithmetic/calculus source, Horn-flow interpretation, and logical calibration remain inherited. Cofinal padding and consecutive-product beta moduli are credited to the incoming Cofinal Witnesses package. The final source composes them with V0=(F²+1)^t and q=(BH0)^K.

These provenance distinctions are explicit in `../direct/PROOF.md`; they are not inferred from finite coefficient checks.

## Unbounded mathematical checks

### Main Pell classification and requested-index degeneracies

The descent proof in `SIGNED_CAP_AUDIT.md` covers all integer norm-one solutions at A²-1, including x<0, y<0, y=0 and independent signs. It does not assume an index is positive before recovering it.

The final literal frame is W=2+Σa², not the doubled frame of an earlier proposal. Its atom list is exactly the set of distinct actual base, exponent and output atoms. The equation t=16+h0² gives W>=258, so the fifteen independent pairs satisfy m<W. For any atom a, W>=a²+2>=2|a|+1 and |a|<W. This proves the needed linear-cap completeness separation for undoubled indices. No positivity of K or an unvalidated output is used here.

The retained A>=0 guard is essential to the stated proof and was checked in the actual source. The odd frame ordinate is nonzero, so the frame norm forces A>=2. Classification at center W+1 and reduction modulo W give A>=X_W(W+1)>W^W and A-1>4W³. Negative A is not silently treated as positive.

Once the anchor has C=Y_W(A), the aggregate C=W+1+Σy_i²+G, G>=0, gives |y_i|<C. Hence each signed principal ordinate is ε_iY_j_i with 0<=j_i<W. The pooled row makes A-1 divide E=Σ(ε_i j_i-k_i)². Since |k_i|<W and m<W, 0<=E<4W³<A-1. Thus ε_i j_i=k_i. Negative and zero requested indices are permitted at this stage; the t-first bootstrap later proves all actual requested indices positive. The sparse companion uses the still smaller signed linear error |ε_i j_i-k_i|<2W<A-1. No quotient sign is needed in either variant.

### The single anchor and a negative comparison center

The exact anchor rows retain C>W, J=C²(e+1)>0 with e>=0, and the norms of (U,C), (H,J) and (S,Q). Hence |H|>=A and the comparison center D=1+4J(2d+1) has |D|>=3. The parameter d need not be nonnegative.

Classify the first two pairs with |U|=X_i(A), C=Y_i(A), |H|=X_l(A), J=Y_l(A). Squared divisibility gives i<=l and C divides l. For comparison classification at |D|, the identities X_j(-a)=(-1)^jX_j(a) and Y_j(-a)=(-1)^(j-1)Y_j(a) absorb the negative center into the two independent coordinate signs. Polynomial base transfer therefore remains valid at D≡A modulo H and D≡1 modulo 4C.

The two comparison congruences give j≡±i modulo 2l and j≡±W modulo 4C. Since C divides l, they imply i≡±W modulo 2C. The strict intervals 1<=i<=C and 0<W<C rule out every possibility except i=W. This includes j=0 as an attempted comparison index; it cannot survive the same congruences. No sign of U,H,S or Q is assumed.

For completeness, choose a positive A-Pell unit power equal to one in the finite ring modulo 8C². It supplies H odd, J>0 divisible by C², and gcd(H,8J)=1. The two correct CRT targets are D≡A modulo H and D≡1+4J modulo 8J. The latter is stronger than D≡1 modulo 4J and is necessary for the odd multiplier. Both targets are compatible. Taking a large positive representative supplies d and comparison coordinates at index W.

### The odd frame restriction

The second-order recurrence Y_(n+2)(W+1)=2(W+1)Y_(n+1)(W+1)-Y_n(W+1) reduces modulo 2W to the recurrence for n. Thus Y_n(W+1)≡n modulo 2W for every positive integer W and every n>=0. In particular Y_W(W+1)/W is odd. Choosing A=X_W(W+1) therefore supplies the restricted ordinate W(2z+1), so deleting its nonnegativity guard loses no required witness. Soundness uses its nonzero absolute value, not the sign of z.

### Linear aggregate completeness

For h=max k_i>=1, the canonical ordinates satisfy Y_(2h)=2X_hY_h>2Y_h² and Y_(2h+1)>(2A-1)Y_(2h)>2(2A-1)Y_h². Since W>=2h+1 and m<W<A,

C-ΣY_k_i²>(4A-2-m)Y_h²>W.

The aggregate slack C-W-1-ΣY_k_i² is consequently nonnegative. In the generic signed lemma the all-zero requested-index case is handled separately by Y_W>W; the actual production source includes t>=16, so h>=16. The ternary representation G=u²+v²+w(w+1) includes G=0 and follows from Legendre's three-square theorem applied to 4G+1. Its nonnegativity holds for every signed integer w.

### Noncircular recovery of power and front signs

The retained factorial remainder/slack and exact-binomial output slack give raw B>=1 and q>=2 before interpreting any binomial or remainder interval. The t ordinate is positive because t>=16. Its actual q^t request excludes a negative abscissa: the power congruence would force m q^t=-1 after the strict frame bound, impossible for an integer m. This proof does not assume m or any digit remainder is nonnegative.

The now oriented t pair recovers V0=(F²+1)^t even if the proposed F is initially zero or negative. The raw ceiling FB=V0+s>0 then gives F>=1, and V0>F² implies B>F, hence B>=2. The cofinal identity y=V0(V0-1) gives y>=F+1, restoring the omitted endpoint slack r0=y-F-1>=0. Only now does the proof use positivity of K=2(2+t+x+y+F). All other exponent constructors are positive from retained front guards and their unchanged monotone gates.

The B^K request orients the K pair; its BH0 request then recovers the new q. Every remaining principal pair supports a q or q+1 request, and the derived t+1 pair is the retained exact one-step addition. Thus all eighteen powers are recovered. At this point each digit denominator L is a positive power of q. The product guard rs>=0 and r+s=L-1>=0 restore both remainder signs, including the cases r=0 or s=0. The raw equation cannot admit two nonpositive values with one strictly negative. Quotient signs follow only afterwards. This order avoids using restored intervals to prove the initial t orientation.

### Self-sized radix and cofinal beta completeness

For H0=1+Σa_i over the nine positive independent representatives, q=(BH0)^K=N H0^K and N=B^K. The bootstrap gives V0<=BF<B²<=N<=q, so the sole exact binomial is carry-free before factorial semantics. The unchanged square-output factorial fixed point gives F=t!. Ordinary range coefficients are below H0^K; the derived-label ledger and ell(t+1)<2F<K give the same strict bound for the derived range. The local majorant and precision-2K CRT proof remain valid. Removing the old aggregate representative bound therefore removes no needed premise.

For a finite refutation, the inherited padding construction admits every sufficiently large horizon. The cofinal family t=16+h0² consequently contains an admissible horizon; mere unboundedness of an unspecified admissible set would not have been enough. At such a padded t, each pending multiset has at most t+1 members and each weight is at most 1+tF<=F²+1=b. Therefore every accumulator is at most b^(t+1), whereas y=b^t(b^t-1)>b^(t+1) for t>=16. Also V0=b^t≡1 modulo F, so F divides y. This is enough for the beta CRT, including its nonnegative endpoint witnesses. The moduli 1+(i+1)y, 0<=i<=t, are pairwise coprime because a common prime would divide a difference at most t and hence F and y, contradicting either modulus.

The choice order is horizon and F, then the prescribed y and a CRT code x, then K,B,N, then the independent representatives, then H0,q, and finally the private Pell witnesses. No later radix or modulus is required to choose earlier data. This establishes completeness of the new cofinal restriction, not merely its soundness.

## Exact compiled artifact checks

`check_compiled_cap.py` imports the previous independent auditor `round15_independent_algebra.py`, not any producing compiler. It checks the following independently from JSON rows:

1. The input equation and raw metadata agree with the pinned round15 baseline. The only permitted raw metadata change is the explicitly identified BH base and its fresh name.
2. Exactly the three intended self-radix power-base rows change; the representative aggregate is the only removed front constraint. Cofinal equations have their exact stated forms.
3. The frame contains every actual semantic atom with its correct affine restoration. Every principal pair and exponent is derived from the literal raw ledger, not accepted from a summary count.
4. All old private comparison constraints removed by the compiler are identified exactly; all retained rows remain unchanged except the documented odd-frame substitution. All new anchor, cap and residue rows are reconstructed exactly. Every principal norm retains its A-times-ordinate gate.
5. Every guard is an exact ternary nonnegativity equation. Every interval pair occurs once. Every algebraic sign-inference step is replayed, and the crucial A, factorial, output-slack, x and representative signs are checked.
6. The inherited Horn factorization is verified by its exact circuit identities and non-escape checks. Every monic projection restoration is replayed, with residual degree checked after every substitution. Every translation is an integral bijection, and the final centered certificates bind to their parents.
7. The entire sum-of-squares quartic is collected again and compared coefficient-for-coefficient. Every final variable occurs, every residual is quadratic, the exact degree is four, and every reported size metric agrees.

The normal and optimized-Python replays agree. Twelve deliberately corrupted controls are rejected, including changes made after recomputing a source hash, so a matching hash is not treated as an arithmetic proof. The separate signed arithmetic controls cover 23,266 finite cases; the odd-anchor controls include negative comparison centers. These finite controls supplement, rather than replace, the unbounded arguments above.

## Natural architecture cross-check

The separate natural construction was also reviewed in `../architecture/UNIFIED_CAP_PROOF.md`. Its factorial bootstrap, horizon-twelve fixed-point extension, K=R budget, self-sized radix, inherited unsigned cap and precision-2K completeness are consistent. The t>=12 estimate starts from 4096>12²·13. An independent replay of its natural-domain projection and complete expansion confirms 249 natural variables, 186 rows, 27,078 monomials and height 85,178,741 for the primary, and 278 natural variables, 215 rows, 5,524 monomials and height 83,852,788 for the sparse companion. These are natural-domain equations, not direct replacements for the 324- and 338-integer endpoints without a domain conversion.

## Reproduction and pins

Run from the release root:

    python cap_audit/check_compiled_cap.py direct/cap_cofinal_self direct/cap_sparse --centered direct/integer324 direct/integer338 --raw direct/portable_input --adversarial --output cap_audit/FINAL_ENDPOINT_CHECK.json

Repeat with `python -O` and a different output path. Also run `python cap_audit/check_signed_cap.py` and `python cap_audit/check_odd_anchor.py`.

The portable baseline files were compared byte-for-byte against the frozen round15 source:

- equation.json SHA-256: 6dac6beef0fbc724f244c85f1e17730b141e96cdaba1b11d9c6528c6a19a8442
- raw_audit_input.json SHA-256: f6602525ef57be22d2b5e8407efd4e000ec9be8b242eb2d0024dc757e2c1f587

The full transitive formal calibration closure was not rebuilt by this audit. Its status remains an explicit inherited dependency rather than a new machine-check claim.
