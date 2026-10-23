# Preliminary non-certification of a 42-integer quartic proposal

Proposal: in Q45 replace the separate positive representations of eta and zeta by one positive representation of their product, saving three variables. This guarantees common nonzero sign but does not yet force positive sign.

The inherited Q45 proof requires eta,zeta>0 before excluding negative s, bootstrapping the first Pell index, proving the ordinary relaxed-rank growth bound, and recovering the power. Thus simply applying that theorem after the new guard would be circular.

In the branch s>0 and eta,zeta<0, put k'=-k and c'=-c. The first Pell classification gives k'=2 psi_P(n), and the original index equation now gives 2n congruent to -R-1 modulo E. With 0<R+1<E, the least positive residue is E-R-1, not R+1. The original n >= (R-1)/2 bound must be replaced and checked before the ordinary rank lemma.

Even if one obtains main rank p=R, the main root relation D-ac=X+gamma H with c negative changes the two root-sign residues: X is congruent to either 2^(-R) or -2^R modulo H. The existing positive-c signed-gamma conclusion X=2^R does not apply. Therefore obtaining E>3R+1 from X=2^R, then using it to exclude the negative branch, is circular. A new pre-recovery growth or modular exclusion could potentially settle the branch, but this review does not supply it.

Status: exploratory only; no 42-variable correctness claim endorsed. Parent continues the ordered-proof investigation.
