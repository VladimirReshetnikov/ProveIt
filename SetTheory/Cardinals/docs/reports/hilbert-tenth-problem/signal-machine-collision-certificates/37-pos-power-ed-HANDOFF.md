# Exact degree: review handoff

The requested candidate is proved for every K, including its exact signs and
the sum-of-squares coefficient. This is a new unnumbered continuation and does
not revise or replace any sealed report.

## Main review points

1. `PROOF.md`, Section 3: finite-difference telescoping at the K-block boundaries
   gives a strictly negative coefficient for even K. For odd K the highest
   coefficient vanishes by reflection symmetry and the next coefficient is
   S_K=sum_h (-1)^(h+1) binom(K^2-3,hK-1).
2. Section 4: the filter uses roots of r^K=-1 and the factor r(1+r)^n, with
   n=K^2-3. The shift by one is essential. After pairing conjugates, its sign is
   (-1)^((K+1)/2) times a positive alternating sum of sin(theta)cos(theta)^n.
3. The uniform inequality is fully elementary:
   1/sqrt(K^2-3)<=sqrt(3/2)/K<3/(2K)<pi/(2K)<tan(pi/(2K)).
   It implies strict decrease at every sampled angle, including K=3.
4. Cleared leading coefficients are a_K=-sum_h binom(N-2,hK-1) for even K,
   and a_K=(N-1)S_K for odd K. The V_0 leading coefficient is -K a_K, from
   V_0=c(z+K)-K U_0, with c=(N-1)!.
5. Section 5: delta_K>=3 and 4delta_K>2N, so the entire highest homogeneous
   part of the six-square polynomial is exactly
   (1+K^4)a_K^4 j^(4delta_K). The acceptance term cannot compete even for a
   full table. At K=1 the separate displayed formula has degree two.
6. Section 6: the original native-gap composition has degree 12 at T=0 and
   the above degree for T>=1. The source support ceiling improves to
   16delta_K+11. Neither statement alters correctness or witness counts.

## Evidence and execution boundary

Only the newly authored `exact_degree_check.py` was run, after full inspection.
It computes integer finite differences and Newton-basis coefficients, verifies
every reconstructed interpolation node, and expands literal polynomial
residuals. It does not import the retained source checker. Its evidence passes
40 K values, 285 interpolation nodes, and 38 complete SOS expansions.

The main source proof, prior native-gap proof, trace proof, physical proof, and
pinned Pell source were read as inert text, with license and provenance.
No upstream scripts, interpreter, physical simulator, or proof assistant was
run. The original source-packet before/after hashes are equal.

The parent has read the full proof and found no mathematical correction.
A separate independent audit is still appropriate before incorporating this
result into a later report. No literature novelty claim is needed or made.
