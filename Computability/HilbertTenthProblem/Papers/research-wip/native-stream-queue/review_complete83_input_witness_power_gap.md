# Independent review of the input-witness power gap

**PASS; no requested change.** I read the entire final helper and companion, the full pinned quotient-dichotomy proof, and the independent-gamma proof's full-zero bootstrap and input-fiber sections. The bound uses the inherited hypotheses before canonical input decoding; it does not assume a noncanonical marker is an ordinary power or an accepted computation.

| Reviewed author file | SHA-256 |
|---|---|
| `complete83_input_witness_power_gap.py` | `f39d68e0f42f39236067aa60dcd0c913f9fbbdb2234b4ddbd1f4d046dc22888a` |
| `complete83_input_witness_power_gap.json` | `97f0e1825c7033efb5378f2e1c40ecf58e34fa01bfb48b38ac2bf59c26633c87` |
| `complete83_input_witness_power_gap.md` | `30a2b5eb4aa5dda7c08df01acd89fca3c4311b91f62e9df1f767341ed670f4f6` |

The two proof dependencies read for the premise check are `complete83_input_quotient_dichotomy.md` (`46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505`) in full, and `complete83_independent_gamma_scout.md` (`bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41`) Sections2–3, with the later alias/scope statements checked. All six dependency byte pins were independently authenticated. This review does not re-establish the deeper native-kernel, normalized-sign or compiler-converse proofs from their original sources.

The notation and domain are consistent. The source register `A` is the discriminant Delta, whereas the Pell parameter in the new proof is A=a+2. The supplied `delta` is an independent positive witness. The source port `sigma` denotes independent gamma; gamma>rho is not imposed. The valid fixed-program recipe and all supplied positive coordinates are still essential.

The inherited full-zero bootstrap first cancels positive Delta in the scaled identity, obtains the normalized factor signs and main rank, and only then recovers X=2^R and the native half-binomial data. Its conclusions include |W|<q and the positive input Pell root without comparing rho with gamma. The dichotomy then obtains 3<=u<R<A, q<A, even A, odd u and the two index progressions. Those are legitimate premises for this follow-up on arbitrary full zeros. Positivity of the literal parent inverse is used only after identifying v=u.

For every noncanonical index, the odd progression starts at u+2Delta and the even progression starts at A*u; since u<A, A*u<2Delta. Thus v>=A*u>=L*R for L=floor(A*u/R). The bound A>2^R, integer R>=7 and u>=3 give L>=55. The consecutive-difference numerator `(R−1)*2^R−1` is positive, so the finite floor samples are not being used as proof of the unrestricted range.

The large coefficient estimates are sufficient with room to spare: c>=psi_A(3)=4A²−1 exceeds Delta, H+q and u. Pell addition gives psi_A(L*R)>c^L for L>=2, and monotonicity transfers this to psi_A(v). The inequalities

    (c−Delta)*c^(L−1)>u,
    (c−H)*c^(L−1)>q

then yield delta>c^(L−1) and rho>c^(L−1), respectively. The second uses `E_v=2*psi_A(v)−psi_A(v−1)>psi_A(v)` and only |W|<q; it is valid for either sign of W. It does not require W=2^u, H-integrality for arbitrary diagnostic indices, or a multiplicative-order estimate.

In the canonical branch, v=u<R gives delta<c/Delta, while the inherited dichotomy gives 0<rho<gamma<c and a strictly positive parent inverse. Since L>=55, either delta<=c^54 or rho<=c^54 excludes the noncanonical branch on the full zero set. This conclusion preserves the same ordinary input. It does not establish soundness for the unrestricted83 language: accepted inputs already have noncanonical completions beyond the gap, and the polynomial does not enforce either power bound.

I independently reconstructed the entire literal84-to83 deletion from the pinned JSON and checked all20 saved boundary rows against the actual83 array. The result is still **83=47M+36A**, eighteen positive witnesses and unchanged full packet SHA-256 `ba7e5024d90b80f82bbfaca1dceda0497cb543f6efd10d0a71edf65ecfc1ba7c`. The new helper's topology/liveness checks cover all83 rows and25 supplied ports. No new circuit is emitted, and degree187 remains inherited.

The finite evidence is accurately scoped: twelve relaxed Pell models,36 delta-numerator inequalities,108 rho-numerator inequalities and74 floor checks. These models are not compiler histories or full zeros. The large-index numerator checks do not claim H-integrality; the canonical congruence checks are separate. I read the binary Pell arithmetic and exact triple-angle checks. The variable exponent L is used only in a mathematical estimate, not as an uncharged circuit primitive.

Fresh normal and optimized exact author receipt replays from `/` passed during this review. The author helper is new and was authorized for replay; no frozen predecessor Python was imported or executed. The review made no repository changes and materialized no full compiler or native Pell tuple. The universal84 bound and unresolved independent-gamma83 language status remain unchanged.
