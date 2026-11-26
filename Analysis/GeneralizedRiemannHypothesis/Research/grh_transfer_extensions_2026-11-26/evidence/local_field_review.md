# Exact torsion costs over wild prime-degree radical coefficient fields

## Deliverables

- `false_tate_section.tex`: complete standalone section, suitable for input into the main paper. Uses standard `theorem` and `proof` environments, AMS notation, and no custom macros.
- `check_false_tate.py`: exact computational checker using SymPy integer resultants. It has no network use and writes a JSON certificate.
- `false_tate_certificates.json`: results for (p,h)=(3,2),(3,3),(3,4),(5,2),(5,3),(7,2), including every coefficient in the pi-power basis and every residue-cancellation step. All tests passed on 2026-11-26.

## Main result

For odd p, u in Z_p^*, K=Q_p(pi), pi^p=p*u, primitive p^h torsion shell z=zeta-1, N=phi(p^h), h>=2, put delta=1/(p-1)-(2p-1)/(p*N). The exact least cost for a packet of integral polynomial witnesses to force positive-part loss greater than epsilon everywhere on the shell is

C = min(1, (floor(epsilon/delta)+1)/p).

The shell h=1 has cost one at every tolerance. Costs add for finite unions of shells. Bounded integral power series have the same optimum. For p=5,h=2, thresholds 4/25,8/25,12/25,16/25 yield costs 1/5,2/5,3/5,4/5,1.

The stronger arithmetic theorem is degree-exact. With n=N/p and alpha=zeta-1,

max_{P monic integral, deg P=m} v(P(alpha)) = m/N + floor(m/n)*delta, 0<=m<N.

All maxima come from a single monic degree-n polynomial B by T^j B^k, m=kn+j.

## Proof-critical details

1. Over C_1=Q_p(zeta_p), K C_1/C_1 is cyclic degree p, with sole upper and lower break p. Uniformizer (zeta_p-1)/pi proves this directly.
2. C_h/C_1 has upper breaks (p-1),2(p-1),... . The character breaks of the two factors are distinct, proving the compositum is totally ramified and giving lower break 2p-1 for E/C_h, hence different exponent 2p(p-1).
3. Do not justify [K C_h:K]=N merely by an intersection formula with only one Galois field. The section instead works over C_1, where both degree-p and cyclotomic extensions are Galois and have trivial intersection. Non-Galoisness of K excludes containment in a cyclotomic field.
4. The order index is I=((2p-1)N-2p(p-1))/2. A maximizing monic degree-n polynomial exists by compactness.
5. Its value b cannot lie in (1/N)Z, by cancellation with pi^t alpha^j. Consequently alpha^j B(alpha)^k have distinct valuations modulo (1/p)Z and form a reduced basis. Computing its integral-basis index determines b and proves all degree maxima.
6. All roots of B have valuation 1/N: otherwise the matching-root subpolynomial has degree less than n, contradicting the optimal bound in that smaller degree. This supplies exact witness cost v(B(0))=1/p.
7. The packet proof handles positive parts individually. Nonmatching roots contribute no positive excess over the Gauss valuation; matching roots form K-rational factors and have additive budgets. This prevents cancellation between losses on distinct polynomials.

## Source connection and predecessor

Upstream at SHA 72fead102f663d5c7a407964a13dc0cf9d977207, `grh/src/New/Congruences/Selmer/RootsOfUnity.lean`, approximately lines 292-343: `exists_rootOfUnity_eval_le_gaussVal_add`. Its docstring and proof choose a shell with few roots of matching valuation, then a torsion point away from those roots. Our exact field-dependent calculation sharpens this local ingredient; it is not an RH consequence.

The direct predecessor is ProveIt `docs/incoming/grh_method_transfers_graph_towers_and_finite_rings.zip`, Git blob 8a901afb0086eb6574bb0d07a9081b3fba3d9907, especially `grh_method_transfers/supplement/wild-cubic.tex` and `check_wild_tower.py`. This already proves p=3,u=1 at all conductors; do not present that special case as new. It states general false-Tate ramification is classical and cites the same literature below. Other supplied report searches did not locate a general odd-prime formula; root should qualify claim as new relative to inspected corpus, not established publication priority.

## Bibliography keys used by section

- `priorGraph`: the incoming packet above, pinned ProveIt d80526e4212e80f52046395005562b12d900dc37. Link: https://github.com/VladimirReshetnikov/ProveIt/blob/d80526e4212e80f52046395005562b12d900dc37/docs/incoming/grh_method_transfers_graph_towers_and_finite_rings.zip . Cite the wild-cubic supplement explicitly.
- `Viviani`: Filippo Viviani, *Ramification groups and Artin conductors of radical extensions of Q*, Journal de théorie des nombres de Bordeaux 16 (2004), no. 3, 779–816, DOI 10.5802/jtnb.470. Primary source https://jtnb.centre-mersenne.org/item/JTNB_2004__16_3_779_0/ and https://arxiv.org/abs/math/0409533 . Search/open IDs available to parent after reopening: turn332235056search0, turn332235056search1, turn332235056academia28.
- `WangYuan`: Shanwen Wang and Yijun Yuan, *Uniformizer of the False Tate Curve Extension of Q_p (II)*, arXiv:2301.09135v2 (26 June 2023), journal DOI 10.1142/S1793042124500015. Primary https://arxiv.org/abs/2301.09135 . Full opened ref turn980824993view0, abstract specifies explicit formulas for Q_p(zeta_{p^m},p^{1/p}) for m>=1. This is classical field arithmetic, not our packet optimization.
- `GMN`: Jordi Guàrdia, Jesús Montes, Enric Nart, *Higher Newton polygons and integral bases*, Journal of Number Theory 147 (2015), 549–589, DOI 10.1016/j.jnt.2014.07.027. Primary https://arxiv.org/abs/0902.3428 and https://doi.org/10.1016/j.jnt.2014.07.027 . Opened refs turn980824993view2, turn749394225search3. Their general reduced-basis theory is acknowledged, not claimed new.

Primary-literature queries for torsion/specialization/false-Tate valuation optimization found no direct matching theorem, but this is not proof of novelty. Both theorem and computational artifacts here are human mathematical derivations/exact arithmetic, not Lean kernel-checked.
