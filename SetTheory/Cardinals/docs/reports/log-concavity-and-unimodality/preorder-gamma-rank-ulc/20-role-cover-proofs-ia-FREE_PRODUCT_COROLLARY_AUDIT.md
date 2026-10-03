# Independent audit: rank-two free-product corollary

Approved, without a novelty claim: if M on S and N on T are loopless rank-two matroids on disjoint ground sets, then M □ N* has a real-stable basis polynomial.

The primary [Crapo–Schmitt paper](https://arxiv.org/pdf/math/0409080), Proposition 1 and the following basis characterization (printed page 2), were independently inspected. Put J=T\K. Dual rank gives rank_N*(J)=|J|−2+rank_N(K). Hence J spans N* exactly when K is independent in N. In that case nullity_N*(J)=2−|K|. For I independent in M, rank-lack_M(I)=2−|I|. The free-product basis equality therefore holds exactly when |I|=|K|≤2. In particular the order of the factors really is M □ N*.

Writing B for a basis polynomial and L for the sum of ground variables, the basis polynomial is

  y^T [1+L_M(x)L_N(1/y)+B_M(x)B_N(1/y)].

It equals y^T H(x,−1/y), where the independently approved stable coupling is H=B_MB_N−L_ML_N+1. Negative reciprocal substitution preserves the upper half-plane; each y has degree at most one before inversion, so the prefactor clears all denominators. The result is a polynomial, nonzero because its y^T coefficient is 1, and real stable. No extension to arbitrary-rank free products is asserted.

Dependency: the rank-two coupling in `../BALANCED_REAL_ROOTEDNESS_PROOF.md`, independently approved and pinned by `balanced_real_rootedness_audit_receipt.json`.
