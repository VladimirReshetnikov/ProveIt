# Independent audit: five-core cubic-two certificates

**Result: PASS.** Executed 2026-10-01; initial elapsed time 5.876 seconds; portable replay passed in 5.853 seconds with four Python worker processes.

## Scope and verified conclusion

For every loopless directed graph H on five labeled core vertices, let F_{kr} be the Boolean endpoint-support polynomial: sum u_S v_J once for each disjoint S,J with |S|=k, |J|=r for which a directed matching from S covers J. The independent reconstruction enumerates all injections of J into distinct vertices of S, with the required arcs directed from tails to heads. Different matching witnesses never multiply an endpoint coefficient.

With sink moments

E1=A+B, E2=AB+B²/2, E3=AB²/2+B³/6,

set γ_k=Σ_r F_{kr} E_{k-r} for k=1,2,3, and G_k=k! γ_k. The checker verifies the exact moment coefficients and scaling

3G2²−4G1G3 = 12(γ2²−2γ1γ3).

The certificate collection proves this boundary polynomial is nonnegative for every nonnegative u_i,v_i,A,B and every such H.

## Certificate results

- 9,608 graph-class files were present, correctly indexed, and matched their stated core rows
- A separate reflexive-transitivity test confirmed exactly 139 preorder representatives
- Across all certificates, the exact remainders contain 15,061,340 positive terms; no remainder is identically zero
- Every stated target was 3G2²−4G1G3
- 57,089 rational binomial-square summands were checked exactly
- Every square weight was strictly positive; every multiplier monomial had nonnegative integer exponents
- Every certificate's full square expansion was subtracted from the independently reconstructed target using exact rational arithmetic
- Every resulting coefficient was nonnegative, including exponents absent from the original target
- Exactly 2,391 certificates were empty, and these were exactly the 2,391 already coefficientwise-nonnegative targets

Each certificate has the form P=Σ_t w_t x^{m_t}(Σ_j q_{tj}x^{a_{tj}})²+R, with w_t>0 rational, nonnegative integer exponents, and R coefficientwise nonnegative. This is a valid nonnegativity certificate on the nonnegative orthant.

## Independent coverage verification

The checker interprets the 20 possible arcs in lexicographic (tail,head) order with unequal endpoints. It recomputed each representative's code from its rows, generated all 120 vertex relabelings, checked that each representative was the minimum of its orbit, checked that distinct listed classes have disjoint orbits, and verified that their union is the entire 2^20=1,048,576 labeled graph universe.

Orbit-size histogram (size: number of classes): 1:2, 5:6, 10:14, 12:1, 15:8, 20:58, 24:3, 30:114, 40:28, 60:1373, 120:8001.

## Independence and reproduction

The verifier uses only the Python standard library. It does not import kernel.py, poly.py, the certificate generator, or any other producer module. It does not use numerical optimization, floating-point polynomial arithmetic, or the producer's feasibility routine.

Run:

python check.py /path/to/universal-sink-five-core /path/to/receipt.json 4

The input directory must contain cores.txt and cubic-two/certificate_0.json through certificate_9607.json. The receipt records source, verifier, and certificate-manifest SHA-256 hashes. A per-certificate manifest is saved alongside the receipt.

Audit files in this directory:

- check.py: portable standalone exact checker
- receipt.json: successful execution receipt and hashes
- certificate-manifest.json: individual certificate hashes and verified counts
- audit.log: execution progress and final receipt

## Limit of this audit

This is an independent exhaustive finite certificate proof for the specified five-core upper-boundary polynomial. It is not a compact ordinary argument. It does not independently establish that every admissible sink-moment sequence reduces to this boundary, verify other rank gaps, or settle the actual-degree-below-five cases. Those remain separate logical steps in any broader theorem.

## Article and portability review

The final six-page article certificate statement, moment scaling, and stronger-constant counterexample are approved in article-certificate-approval.json, pinned to both TeX and PDF hashes. A separate matching-state dynamic program confirmed the literal counterexample script. The updated checker defaults to ../certificate-data relative to its own location; if absent, it requires an explicit data directory. No prior archive or absolute source fallback exists. The staged checker was rerun successfully with no source argument.
