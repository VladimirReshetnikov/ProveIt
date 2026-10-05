# Independent review of the distinct-scale doubling fixed-point obstruction

**PASS within the stated full-action interface; no mathematical correction requested.** I read the complete final 218-line proof, its complete metadata receipt, and the three pinned predecessor notes as inert text. The all-degree unequal-scale theorem and its smooth finite-order corollary are sound. This is a proof review, not a numerical test or a new integer compiler.

## 1. Frozen material and scope

| Material | SHA-256 |
|---|---|
| /tmp/markov_distinct_scale_fixed_point_obstruction.md | 4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb |
| /tmp/markov_distinct_scale_fixed_point_obstruction.json | 048c36ed52d88a27a6965e092614c0e86ae5c83898e4896df215e089feba5cb5 |
| markov_doubling_mixed_subspace_boundary.md | baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063 |
| markov_distinct_scale_fourier_boundary.md | 23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee |
| markov_distinct_scale_first_profile_exclusion.md | 33231c7f6306a5ad2c6b64a1bf809a2ccee08f7e87274e285ff93ca62d3b8850 |

The three WIP basenames belong to Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue. Fresh byte checks bind these exact files and their sizes/line counts in the companion review JSON. Only the common-scale note is needed for the equal-scale part of the final corollary; the other two notes are historical bounded results, not premises of the new unequal-scale argument.

The exact prohibited interface consists of continuous strictly positive normalized real doubling masks a,b, independent real finite-trigonometric functions f,g, and

    T_a f=lambda*f,       T_a g=lambda*g,
    T_b f=mu*f,           T_b g=mu*(g-f),

on all of span_R(f,g), with distinct positive lambda,mu. The identity-only example remains valid and is correctly distinguished from this pair.

## 2. Independent algebra and local proof challenge

I rederived the determinant identity without dividing by an odd part, a mask difference, or a common factor. Put f2(x)=f(2x), g2(x)=g(2x), delta=mu-lambda, and kappa=mu/delta. The normalized formulas give

    f-lambda*f2=(2-a)*f_o,
    g-lambda*g2=(2-a)*g_o,

and the two mask differences give

    f_o*g2-g_o*f2=kappa*f2*f_o.

Hence

    f*g2-g*f2=kappa*f2*(f-lambda*f2).               (R1)

Both signs agree with the stipulated decrement g -> g-f.

The author's rational proof is valid at every possible zero multiplicity. A nonzero Laurent polynomial F has F(z)=(z-1)^r U(z) near 1, with r>=0 finite and U(1)!=0. Thus F(z^2)/F(z) is regular with value 2^r. Any pole of G/F of order s>=1 leaves a nonzero coefficient proportional to 2^(-s)-1 in its difference under z -> z^2. Consequently that ratio is regular at the fixed point, and the rational identity forces lambda*2^r=1. No assumption about the location or removability of a common Laurent factor is hidden here.

I also obtained the scale relation directly from Taylor coefficients, independently of that meromorphic-ratio proof. Suppose

    f(x)=A*x^r+O(x^(r+1)),
    g(x)=B*x^s+O(x^(s+1)),

where A,B are nonzero and r,s are their finite vanishing orders. The leading term of the left side of (R1) is

    A*B*(2^s-2^r)*x^(r+s).

If s<r, this has order below 2r, whereas the right side of (R1) is O(x^(2r)), a contradiction. If s>=r, the left side is O(x^(2r+1)); when s=r its displayed leading coefficient vanishes. The coefficient of x^(2r) on the right is therefore zero:

    kappa*2^r*A^2*(1-lambda*2^r)=0.

All factors other than the final parenthesis are nonzero. Thus again lambda*2^r=1. This argument covers repeated and shared zeros without any division by f or g.

Finally, normalization gives exactly

    a(x+1/2)*(f(x+1/2)-f(x))
        =2*(lambda*f(2x)-f(x)).

The right side is O(x^(r+1)); continuity and a(1/2)>0 make the coefficient on the left bounded away from zero. Hence f_o=O(x^(r+1)). Boundedness of b-a then conflicts with

    (b-a)*f_o=delta*f(2x),

whose right side has nonzero order-r coefficient delta*2^r*A. The r=0 case is included: one side tends to zero and the other to a nonzero constant. No regularity of the masks beyond continuity is used in this order comparison.

## 3. Smooth corollary and equal-scale boundary

The separate smooth corollary is also correct. If the common eigenvector f is smooth and has finite vanishing order r, the Taylor comparison above applies when g has finite order. If g is flat, its estimates to every finite order instead make both determinant terms O(x^(2r+1)); the same scale relation and contradiction follow. Thus any hypothetical smooth unequal-scale escape must have f flat at x=0. Flatness of g is not an unhandled exceptional case, and the theorem does not claim that flatness of f suffices for a construction.

For equal scales, the pinned earlier proof correctly uses a shared nonconstant finite-trigonometric eigenvector to identify the two continuous normalized masks. The eigenvalue-one boundary is handled by the strict-positive averaging maximum principle. Combining that theorem with the new unequal-scale argument therefore excludes the stated finite-trigonometric pair at every pair of positive scales.

The mask positivity requirement is substantive, particularly at x=1/2 in the local contradiction. The review does not infer a counterexample or a theorem for nonnegative masks with zeros, arbitrary continuous coordinate functions, flat smooth coordinates, unnormalized operators, state-dependent charts, or actions prescribed only on a selected ray or line.

## 4. Relationship to prior results and computation

The earlier 2m/3m and Laurent-gcd restrictions, and the first-profile exclusion, remain correct bounded theorems. The new argument settles the profiles that those notes explicitly left unresolved. It does not retroactively turn their bounded claims into errors, nor is their degree classification needed to prove the new theorem.

No full-action pair is constructed; no gate count, witness bound, loader, ordinary-input map, variable program or unbounded history is improved. The result is a representation obstruction, not a blanket restriction on Turing-complete substrates or Diophantine methods.

This review used only inert proof/receipt reads, independent symbolic reasoning, and fresh byte metadata. No author helper, predecessor helper, archived or supplied program, copied program, saved array, or builder was executed or imported. No numerical search, source-array evaluation, repository change or Git mutation occurred. No false statement requiring a retained correction was found in the final author note.
