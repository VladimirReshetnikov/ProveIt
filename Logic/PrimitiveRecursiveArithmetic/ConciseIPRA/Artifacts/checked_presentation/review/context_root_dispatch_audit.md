# Audit: hypothesis-root dispatch

Proposed replacement:

    (m or len(a) == 2) and k

by

    (len(h) > 1) and k

where h is the freshly constructed but not yet opened context entry.

## Blocking issue: ternary introduction matrices

The inherited sorted decoder gives a ternary formula [P,U,B] the meaningful
interpretation Q_y B. It is not administrative truth. On an introduction
packet with m=0 and u=0, h is the instantiated introduction matrix. If that
matrix has arity three, the old selector chooses the zero instance (case
introduction), but the proposed selector chooses the fresh parameter
(progress introduction).

The changed rule therefore includes

    Gamma, Q_v B(t,z,v) |- Q_v B(t,S z,v)
    ---------------------------------
         Gamma |- D_(x,y) Q_v B(x,y,v)

with the usual fresh z. This is an induction principle for a quantified
matrix, whereas the inherited rule allows progress only for literal
equations. The arity-three case cannot be justified by the surplus-arity
truth convention: that convention begins at arity four.

Restricting the externally presented goal to guarded Eq/D is insufficient.
The recursive major premise m is certificate-supplied and can be a unary D
whose body is a ternary Q. Intermediate objectives are not checked against
the public Eq/D grammar. The added Q-progress rule can therefore be used
inside proofs whose final public goal is canonical.

There is reason to expect a real strengthening, not just a missing trivial
lemma. Native formulas can be gated into closures Q_v gate_v(A) with a
provable zero instance and with the nonzero instance equivalent to A. The
unchanged public Eq/D fragment proves the logical conversions. Induction on
those Q formulas can then implement induction on the represented A. A
complete separation proof has not been formalized here, but the proposed
soundness claim already fails to follow from the existing induction theorem.

## Other branches

- Major export of D produces ternary Q: opening at the fresh witness is
  correct and necessary.
- Major export of an equation or Q produces arity six or nine: both are
  administrative truth.
- Computation supply produces binary equality. Opening it at the fresh
  parameter can be justified by the inherited known-zero-instance supply
  lemma, even when it is not uniformly an arithmetic theorem at that fresh
  parameter. It is safer to cite that lemma than to claim uniformity.
- Introduction of a unary D matrix correctly receives case mode.
- Introduction of a binary equation correctly receives progress mode.
- Empty matrices are truth; surplus matrices of arity at least four are
  truth. Changed dispatch on those shapes is harmless semantically, subject
  to successful traversal and the existing scope invariant.

## Verdict

Do not accept this replacement for the current compact certificate language
without an additional theorem or restriction. Its arity-three intro case
adds a quantified progress rule. A separate clausal syntax in which Q is
only a context form could avoid that ambiguity, but the enforcement and
translation cost would have to be included in the checker comparison.
