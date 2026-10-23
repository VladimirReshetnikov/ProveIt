# A degree-111 evaluator with fifteen positive unknowns

The circuit [`circuits/p69_unscaled.json`](circuits/p69_unscaled.json) gives a
69-operation polynomial of exact degree 111. On the positive domain it has
exactly the same zeros, at the same coordinates, as the report's P₆₇. The
local algebraic equivalence is proved in
[`ShortEquation.lean`](Lean/DiophantineConsistency/ShortEquation.lean).
[`ShortCircuit.lean`](Lean/DiophantineConsistency/ShortCircuit.lean) embeds
both literal gate schedules, defines the actual `MvPolynomial (Fin 15) ℤ`,
and proves that its evaluation vanishes exactly when P₆₇ vanishes.
The native-window compiler and its coefficient calibration are inherited
ordinary mathematical arguments, and are **not** given an end-to-end Lean
certificate by this construction. This note consequently does not claim a
new kernel-checked equivalence with Con(ZFC).

This is a degree/operation tradeoff, not an operation-count record or a
minimality theorem. P₆₇ has degree 155 and costs 67 operations; its reduced
auxiliary version P₆₈ has degree 123 and costs 68. The unscaled version here
has degree 111 and costs **69**, because the auxiliary coefficient loses the
old strong factor's shared multiplication `Delta*f^2`.

## Fixed coefficients and equation

Take the **whole** coefficient tuple from report package
[`36-small-tuple/coefficients/COEFFICIENT_BINDING.json`](con-zfc-diophantine-forms/36-small-tuple/coefficients/COEFFICIENT_BINDING.json).
Its four ports are `beta = B-1`, `K0 = DC+B*DR`, `MC`, and the **shifted**
`MF = MF_native+B-1`. In that tuple `B = 2^1012115`; the finite coefficient
recipe never tests consistency or searches for a refutation. Do not splice
components from different tuples.

All fifteen unknowns are strictly positive integers:

```
J, F, alpha, z, f, h, i, T, s, w, tau, eta, zeta, y, gamma.
```

The following are polynomial abbreviations, not additional unknowns:

```
q = beta*J+1,        C = q-F-alpha,
X = w*q,            Y = s*q^3,       E = X*Y,
k = eta+zeta,       c = k*Y+eta,     a = E+Y,
H = 4*a+3,          Delta = a^2+H,
D = X+a*c+gamma*H,
G = (q-1)*(q-F)+alpha,
R = G*(q^2-1)+(MC+q*MF)*J,
V = c*(T*f-1)-R*f^2.
```

Define six factors:

```
N0   = tau^2-(X*Y^2)*(X*Y^2+1)*k^2,
N1   = D^2-Delta*c^2,
Na   = Delta*(f^2-1)*(V^2-y^2)+y^2,
Nk   = k-h*E-R,
Nt   = (K0+w)*C+(q-F)-z*(q-1),
Ns   = f^2-Delta*(i*c^2)^2.
```

The proposed equation is

```
N0*N1*Na*Nk*Nt*Ns - 1 = 0.
```

Only fixed nonnegative exponents occur. The supplied JSON gives a
self-contained division-free evaluation DAG, including the operations
needed to compute every abbreviation.

## Local correctness and the remaining semantic boundary

Before imposing the equation, positivity gives `a>0` and
`Delta=(a+1)*(a+3)>0`. The report's P₆₈ is identically `Delta` times the
polynomial displayed above. This cancellation therefore preserves its
complete positive zero set.

For completeness, the passage from P₆₇ to P₆₈ also admits a local proof.
After canceling `Delta` at any zero, `Ns` is an integer unit. Since
`Delta=(a+2)^2-1`, square residues modulo four exclude `Ns=-1`; hence
`Ns=1`. It follows that

```
Delta*(f^2-1) = Delta^2*(i*c^2)^2,
```

so the reduced and original auxiliary coefficients agree at that same
point. The argument works in both directions. This is the scope of the
Lean algebra proof. The restriction `Delta != 0` matters for general signed
assignments; positivity supplies it here.

The reports' additional assertion that the resulting zeros encode precisely
finite ZFC refutations still depends on the native-window/Pell compiler.
That compiler has not been formalized by the report or this evaluator.
The independent nine-variable formal route is developed separately in
`Polynomial.lean`; its existence-based coefficient selection is a different
construction.

## Exact operation and degree certificate

Run the deterministic generator and finite audit from the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_short_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_short_circuit.py
python3 Computability/DiophantineConsistency/tools/build_short_lean.py
```

The audit checks the actual exported graph, every gate's operands, all
fifteen witnesses and four ports, full liveness, the source hash, and the
literal transformation from the pinned P₆₇. It records **40 multiplications,
15 additions, and 14 subtractions**. Its exact sparse polynomial identity
check handles the cancellation in `N1`; leading homogeneous arithmetic
then checks all other gates without evaluating a putative zero.

The six exact factor degrees are respectively `22,18,28,7,2,34`, summing
to 111. Put `Q=beta*J` and `C1=Q-F-alpha`. The full leading homogeneous
form is

```
-8*Q^63*h*gamma*i^2*(eta+zeta)^9*w^9*s^18*T^2*f^4*(w*C1-z*Q).
```

The monomial

```
J^64*h*gamma*i^2*eta^9*w^9*s^18*T^2*f^4*z
```

has coefficient `8*beta^64`, nonzero for the fixed positive `beta`.
Thus the upper bound is attained. The generated ledger is
[`circuits/p69_unscaled.audit.json`](circuits/p69_unscaled.audit.json).
These finite circuit and degree checks supplement the Lean polynomial theorem;
they do not certify the compiler semantics or consistency.

## Historical comparison

The reports already cancel `Delta` in their proofs. For example, wave 1
package `08-start-only67` checks the scaling identity in
`evidence/diophantine_zfc_root/audit_inputless.py` at commit `f3af223ef7`.
P₆₇/P₆₈ and the reduced auxiliary coefficient occur in wave 1 package
`06-blank67`, with the proof preserved in wave 5 package 36 at
`proofs/INHERITED_P67_PROOF.md`, sections 2 and 9.

Inspection of the audited wave snapshots `f3af223ef7`, `5b0c9ae9fd`,
`a477d0fc8b`, `52f475c7a7`, and the current wave-5 tree found no stated
15-variable, degree-111, 69-operation evaluator. This is a bounded source
audit, not a priority claim or a proof that no equivalent evaluator existed.
The contribution here is an explicit paid circuit and local Lean
zero-equivalence proof for an already available normalization.

