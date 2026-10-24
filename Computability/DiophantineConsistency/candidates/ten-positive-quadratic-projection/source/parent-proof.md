# Ten positive unknowns, degree816,122 operations

This separate evaluator computes exactly the frozen123-operation
`ten-positive-scaled-norm-shared` polynomial. It has **10 strictly positive
unknowns**, exact degree **816**, and **122 live binary operations**:
73 multiplications,30 additions and19 subtractions. The complete original
compact44 fixed tuple is retained under `coefficients/`; the fourth port
MF is already shifted once.

The literal equation is the final output `N=0` of `equation.json`, with

```
j,F,alpha,i,T,w,Y,n,eta,zeta > 0.
```

Every gate, unknown and port is live. The saved operation does not change
the polynomial, the witnesses, the domain or the fixed coefficient bytes.
The frozen123-operation evaluator and the one-page scaled10 PDF remain
untouched.

## Exact cancellation and complete circuit identity

The parent begins with

```
J=2*j+1;  bJ=beta*J;  q=bJ+1.
```

Later it computes `qm1=q-1`. Delete that subtraction and replace **every**
use of `qm1` by the already available `bJ`. For every commutative ring,

\[
(\beta J+1)-1=\beta J.
\]

For arbitrary inputs, start with equal values at all input registers.
Before the removed gate, all retained definitions are identical. At the
removed gate, the displayed identity equates the parent's `qm1` to the
child's `bJ`. At each subsequent retained gate, its two operands either
refer to unchanged earlier registers or replace this one alias by its
equal value. Addition, subtraction and multiplication preserve equality.
Induction along the finite gate list proves equality at every retained
register and at N. This proves a universal pointwise polynomial identity;
no positivity or special numerical port value is used in this argument.

`PREFIX_REMAP.json` records every parent and child index and register.
The independent checker requires complete ordered coverage, the exact
earlier definition of q, and the precise operand substitution at every
gate. It rejects a changed earlier definition, one incorrect retained
operand, a missing remap entry and a reversed subtraction. The sparse-ring
oracle also verifies the cancellation identity exactly.

## Degree, binding and ordinary correctness

The original proof and independent peer review are retained in
`source/original-proof.md` and `source/original-peer.md`. The full original
normal/-O author replay receipts are `source/original-replays.json`.
The123-operation parent's own receipts and provenance are copied too.
The complete parent equation is pinned by SHA256

```
327296a42616d5646502e9487075be32fe14402dbbad5b2925c8d8ff2718a371
```

The universal identity transfers the original ordinary positive-zero
equivalence with its inherited source61/native-calibration hypotheses.
It also transfers the degree816 upper bound and nonzero leading form at
the actual positive beta. Independently, `check.py` verifies the complete
28-gate tail as the495-term product of all16 norm conjugates. Its425-term
centered expansion has unique weight816 term omega^8 with coefficient1.
Two whole-circuit lines at the actual fixed tuple attain degree816 modulo
large primes. These line controls supplement the unbounded leading-form
argument; they are not used to infer a degree upper bound. The syntactic
degree bound remains928.

The checker authenticates all four complete original compact44 payloads,
compares every retained register on100 signed-input actual-tuple controls
and50 signed free-port controls, and checks the generated artifact seals.
It imports only the independently written sparse-ring helper copied from
the frozen parent peer. No author builder or verifier is imported.

The identity holds before specialization, so the same122-operation
schedule also evaluates the polynomial of the separately calibrated
`one-page-scaled10` BFS44 tuple. That page's K differs from the original
compact44 K used in this packet: this statement does not equate those two
numerical specializations. It transfers this evaluator identity at either
choice of ports. The page's published123-operation evaluator remains
correct, and this minor saving does not require a page rerender.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_scaled_reuse.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm-reuse/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_scaled_reuse.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm-reuse/check.py
```

All four commands pass; `VERIFICATION.json` retains their receipts and
`MANIFEST.json` seals all packet files. No global operation minimum is
claimed. Lean formalization remains paused, and this ordinary arithmetic
identity does not supply the outstanding internal-ZFC derivation or a
proof of consistency/absence of zeros.
