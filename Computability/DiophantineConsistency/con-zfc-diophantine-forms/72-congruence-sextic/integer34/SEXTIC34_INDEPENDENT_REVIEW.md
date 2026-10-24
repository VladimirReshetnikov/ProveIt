# Independent review of the 34-integer sextic

## Finding

No defect was found in the local integer zero-set bijection, residual count,
degree, or supplied full expansion. The new polynomial has 34 unrestricted
integer variables and is the sum of squares of 19 residuals of degrees at
most three. Its exact degree is six, with coefficient one at I^4 g^2.

The parent is the whole source64 Q41 instance. Its fixed tuple is the
source34 mixed-parity-unrounded-1064921 tuple. It is different from the
compact590069 tuple used by the new positive13 equation; the two bindings
must remain separate.

## Method

The reviewer read PROOF_SEXTIC34.md, every source and target residual, and
the inherited Q41 proof boundary. A separate standard-library checker uses
its own AST parser and tuple-exponent sparse arithmetic. It imports neither
the builder nor the upstream polynomial-arithmetic implementation. It
recomputes every restoration identity and independently expands the final
sum of squares into 368 symbolic-port monomials; these match the supplied
expansion exactly.

Files checked:

- Source quartic41.json SHA256:
  a1b5d9bacff52bd864695bd89646cb81eabdee1685b5ebc0348f594f40f4ff82.
- New sextic34.json SHA256:
  955117dee7ee004329b5e613b5f4eea5b30678d5d45f485faaff73f7e8ae47be.

The machine-readable receipt is SEXTIC34_INDEPENDENT_AUDIT.json.

## Why the projection is an exact bijection

Seven source coordinates have unique integer-polynomial reconstructions:
P=k+E(c-eta), X=2u^2, N=q(L+1), C2=c^2,
Delta=a^2+4a+3, V=fo-c, Baux=I^2. The seven defining source rows become
identically zero under these substitutions. The two surviving norm roots
are changed by triangular shears, tau_old=tau+E(c-eta) and D_old=D+ac.
Their inverses subtract the same integer polynomials. No sign or
divisibility premise is introduced by either shear.

Every retained source row becomes its target residual, except for source
row17, V^2+g-y^2. Its target image differs by exactly
o^2(F2-f^2); the residual F2-f^2 remains in the system. Thus both row
systems vanish together. The apparent use of F2 in place of f^2 is a
reversible elementary row operation, not a pointwise polynomial identity
without the retained equation.

Conversely, every Q41 zero supplies the seven defining values uniquely,
and the inverse shears yield all target residuals zero. The two maps are
inverse on the full integer zero sets, with no positivity assumption.
Over integers, vanishing of a sum of squares is equivalent to simultaneous
vanishing of its residuals, so this transfers to the single equations.

## Exact degree

Independent expansion gives residual degrees
2,2,3,3,2,3,2,3,3,2,2,2,3,3,3,3,2,2,2.
All fixed ports have witness degree zero. The term -I^2 g in the auxiliary
norm is the unique residual term involving both I and g. Its square
contributes I^4 g^2 with coefficient one, and no other residual can change
that coefficient. Therefore the exact degree remains six after the actual
native coefficient specialization.

## Logical boundary

This audit certifies the new local reduction over all integers. The passage
from Q41 to existence of a finite syntactic ZFC refutation is the inherited
ordinary proof in PROOF41.md and its explicit PROOF44, native, Pell and
machine-calibration dependencies. The new reduction adds no semantic
assumption and is elementary algebra formalizable in ZFC. Neither this
finite audit nor the new construction is an exported object-language ZFC
derivation or a newly checked complete Lean/Rocq certificate. The local
bijective reduction does not require a new Pell or sign-recovery lemma.

The review was performed by a separate AI-assisted worker in this session;
it is not external peer review.
