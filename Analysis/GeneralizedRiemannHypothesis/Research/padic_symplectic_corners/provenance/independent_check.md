# Independent mathematical referee check

Reviewed `sections/mathematics.tex` independently after its formulas had been proposed. No mathematical error found in the stated exact two-frame density, total variation, Smith distribution, general overlap codimension, or precision-uniform lifting estimate.

## Density and endpoint correction

For N=2g-2, a uniform first complement vector has coordinate-content valuation r<e with probability (1-q^-N)q^-Nr. Conditional pairing with a second uniform vector is uniform on the ideal pi^r R_e. The zero first vector has mass q^-Ne and makes pairing exactly zero. Multiplying by q^e yields precisely the finite-e density numerator, including q^{-(N-1)e} 1_{t=0}. Omitting this term would be an error; it is present in the draft.

Pairing-one full frames have cardinality q^{(4g-1)e}(1-q^-2g). This gives the density denominator and q^-4e matrix mass. Symplectic basis extension is valid over arbitrary local rings with the given unimodular alternating form, without dividing by two. A pairing-one frame is automatically primitive, but primitivity alone does not imply pairing one. The draft correctly uses the stronger symplectic-frame assumption.

## Total variation and Smith types

Let alpha=(1-q^-N)/(1-q^{-(N+2)}). Density equals alpha<1 on det A not congruent to 1, and exceeds 1 on det A congruent to 1, including q=2,N=2 and finite precision e=1. The iid probability of the latter event is (q^2-1)/q^3. Thus TV=(1-q^-1+q^-3)(1-alpha), exactly as stated.

All matrices singular modulo pi have unit defect 1-det A, hence constant density alpha. All nontrivial cokernel probabilities are therefore multiplied by alpha. The independent-entry Smith probabilities in the draft sum to one and follow from valuation of common entry content, rank-one reduction, and a unit pivot making the remaining determinant coordinate uniform. No change is needed in residue characteristic two.

## Full hierarchy of precision corrections

For k>=1 and e>k (also e=infinity), let tilde_mu_{k,e} be the uniform lift of the law mod pi^k. The exact stronger statement is

TV(mu_e,tilde_mu_{k,e})=(1-q^-1)(1-alpha)q^{-Nk}.

Only the shell v(1-det A)=k has negative density difference. On this shell the difference of likelihood numerators is -q^-N q^{-k(N-1)}. The iid shell mass is ((q^2-1)/q^3)(1-q^-1)q^{-(k-1)}. All deeper defect shells have positive difference; this uses 1-q^-1-q^-N>0, valid already at q=2,N=2. Multiplication gives the displayed formula. The optimal positive event is defect divisible by pi^{k+1}.

## General rectangular lifting

With S modulo pi fixed, symmetric bilinear forms restricted to V times U have image precisely the cross pairings whose restriction to T times T is symmetric, where T=U intersect V. This imposes binom(dim T,2) independent conditions; no diagonal conditions arise even in characteristic two. The group lifting fibers are uniform copies of the symplectic Lie algebra. Surjectivity of the first differential therefore gives uniform digits at every precision, and failure is already visible at the second digit.

Minor expository suggestion: when lifting an approximate symplectic matrix with error E, specify right multiplication by I+pi^j A to obtain A^T J+JA=-E without an extra conjugation. Subsequent left perturbations for the compression differential are separately valid.

The isotropic and nondegenerate plane counts, their orbit averages, and the union/first-moment bound for dim(U intersect V)>=2 all agree with direct counting. Sharp O(q^-4g) is proved for TV(actual law, uniform lift). It is not proved sharp for the increase in TV from iid uniform; the two-frame example has zero such increase. The draft's wording correctly attaches sharpness to lifting error and should retain that distinction.

## Exhaustive checks

`code/independent_ring_check.py` independently enumerates all ordered pairing-one frames in four-dimensional symplectic space, rather than sampling symplectic groups or merely reevaluating the density formula. Every 2x2 output likelihood was compared in exact rational arithmetic.

- Z/4Z: 15,360 frames, 256 output matrices, TV=1/8, alpha=4/5.
- F2[t]/(t^2): 15,360 frames, 256 output matrices, TV=1/8, alpha=4/5.
- F4: 16,320 frames, 256 output matrices, TV=49/1088, alpha=16/17.

The cases cover mixed characteristic, equal characteristic with nilpotents, and a nonprime residue field. All exact comparisons passed. See `results/independent_ring_results.json`.

## Novelty scope

A targeted literature search located neighboring work on truncated Haar GL_N(O) matrices, eigenspaces of classical groups over finite rings, and local representation densities. It did not locate the specific compression likelihood plus precision-independent TV and exact lift hierarchy. This is evidence for cautious novelty wording, not a proof of historical priority. The result is unconditional and uses symplectic/local-ring methods related to the supplied GRH sources; it does not imply another RH statement.

## Final additions review

The taller 2a-by-2 corollary, exact threshold probabilities, numerical examples, and sharp universal 8/5 rejection envelope were also checked after integration. No substantive corrections were needed. All examples in the paper agree with the exact formulas. This review is part of the same research workflow and is not external peer review or proof-assistant certification.
