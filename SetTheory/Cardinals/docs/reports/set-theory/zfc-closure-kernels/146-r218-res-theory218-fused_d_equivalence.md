# A single row for universal instantiation and explosion

## An exact logical equivalence

Write \(P=Q_i A\), and retain the released classical implicational row
\(L\). Define

\[
 D(i,A)=((Q_i A\to F)\to F)\to A.
\]

The following three formulas are derivable using **only** the retained
implicational row and modus ponens:

\[
\begin{aligned}
D(i,A)&\to(Q_i A\to A),\\
D(i,A)&\to(F\to A),\\
(Q_i A\to A)&\to((F\to A)\to D(i,A)).
\end{aligned}
\]

Therefore replacing the original rho6 by the single scheme D gives
exactly the same theorem set as replacing it by T and explicit explosion.
All other axioms and inference rules may be retained unchanged. This is
an equivalence of the two *modified* calculi. It does not establish their
consistency equivalence with the original native calculus or ZFC.

Here is a short proof of all three implications. The deduction theorem is
used only in the pure implicational subsystem, so there is no hidden
generalization rule applied to an open assumption.

1. Assume D and P. Under a further assumption \(P\to F\), modus ponens
   gives F. Discharge that assumption to obtain \((P\to F)\to F\), and
   apply D to get A. Discharging P and D gives the first implication.
2. Assume D and F. The K combinator gives \((P\to F)\to F\), so D gives
   A. Discharging the assumptions gives the second implication.
3. Assume \(P\to A\), \(F\to A\), and \((P\to F)\to F\). Under an
   additional assumption \(A\to F\), composition gives \(P\to F\),
   hence F and then A. Discharge \(A\to F\), obtaining
   \((A\to F)\to A\), and use Peirce's law to obtain A. Discharging the
   first three assumptions gives the third implication.

For an independently checkable finite certificate, all three proofs have
been expanded using only these schemes:

\[
\begin{aligned}
K(X,Y)&=X\to(Y\to X),\\
S(X,Y,Z)&=(X\to(Y\to Z))\to((X\to Y)\to(X\to Z)),\\
P(X,Y)&=((X\to Y)\to X)\to X.
\end{aligned}
\]

The inherited `CD230.v` proves `thm_K`, `thm_S`, and `thm_P` from rho8
alone. Substituting their derivations for each corresponding certificate
leaf transports the proof into the native calculus. No use of the deleted
rho6, falsum explosion, quantifier normality, or a semantic completeness
assertion is hidden in this transport. F is an arbitrary formula parameter
throughout this purely propositional proof.

The retained certificate has **211 nodes**, consisting of **106 explicit
K/S/Peirce instances and 105 modus ponens steps**. Its three roots are
nodes 44, 72, and 210. The verifier checks exact formula structure and
earlier-node references; it performs no unification, proof search, or
truth-table inference. Run

```sh
python3 certify_fused_d.py --verify-only
```

The code-level exceptional identity \(I(0,0)=0\) causes no difficulty:
the certificate is a schematic proof under arbitrary substitutions into
the native implication constructor. Specializing P to \(Q_i A\) is valid
even though P then contains A.

## Literal source construction

The old rho6 emitter has 283 primitive occurrences. In the published
219 source, its exact primitive interval is \([895,1178)\), with zero-based
half-open indices. The relevant closed macro word is

```text
binder, binder, matrix, Q, N, Q, N, matrix, I.
```

The binder and matrix pushes each have 26 leaves, Q has 29, N has 47,
and I has 27. The first binder push is the closed interval
\([895,921)\); the outer Q is \([1049,1078)\). Deleting those two
closed fragments produces

```text
binder, matrix, Q, N, N, matrix, I,
```

which emits D and has 228 leaves. The full primitive word decreases from
4,744 to 4,689 leaves. The axiom operation still emits ten outputs.
Other than the altered axiom formula, its source interface is unchanged.

The exact two-deletion layout has 207 source DAG nodes, but its preserved
hardware row cost is 222: the bare cost is 220, and two inherited helper
roles cannot be covered by its live source nodes. It also has a nonzero
context penalty. This is why a shorter primitive word is not itself a
smaller binary machine.

The finite layout census varied the ordered binder/matrix parameter
assignment over six choices, tested both whole-row splice locations,
and distributed the seven macro atoms over the three original closed
source chunks. Together with the exact deletion, this gives **103
layouts**. The minimum protected hardware bound is **221**, with 208 DAG
nodes and zero helper or context penalties. The minimum DAG count alone
is 207. The best bound is still three states above the requested 218.

Two further three-implication fusions with a single occurrence of P are

\[
 ((P\to A)\to F)\to A,
 \qquad
 ((F\to A)\to P)\to A.
\]

Both are propositionally equivalent to D, and each has a 234-leaf emitter.
A further **318 layouts** have minimum protected hardware bound **222**.
These are exhaustive counts only for the stated finite layout families;
they are not lower bounds over all emitters, source trees, or machines.

For comparison, emitting T and explosion as two separate rows uses only
207 leaves in place of 283, but increases the axiom output count from ten
to eleven. The 72 whole-row layouts have minimum hardware bound 226; the
756 layouts preserving the three original closed chunks reach 222.

All these counts use the repaired `hardware_objective219.py`, which
accounts for the duplicated logical `(CD6,CC2)` at native states 13 and
108 and preserves the classified engine/helper rows. The model was
calibrated against the literal 219 table before each screen. It is an
exploratory preserved-row bound, **not** a compiled table or runtime proof.
No altered-calculus machine from these screens is presented as satisfying
the 218-state task.
