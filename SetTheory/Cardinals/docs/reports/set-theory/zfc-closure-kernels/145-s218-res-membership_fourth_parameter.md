# Three smaller source grammars with an unresolved logical calibration

## Exact proposed calculi

The original propositional row is

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

Let a,b,c be the raw natural-number codes of A,B,C respectively, and
let R(i,j) be the native code of the membership atom between the
variables with numerical labels i and j. The three proposals replace
the independently read fourth formula code by, respectively,

\[
U=R(a,b),\qquad U=R(b,c),\qquad U=R(c,a).
\]

These are three separate calculi, not three rows added together.
All other native logical rows, the full support-bearing K bundle,
the original bundle gate, modus ponens, theorem generalization, and
the target code F=1 are unchanged.

The formula codes a,b,c serve two different roles here. A denotes
the formula decoded from a, while the first proposal's U uses a as
a *variable label*. One cannot replace this exact coupling by an
independently selectable fresh atom without proving an additional
theorem.

## Source construction and measurements

The independently read fourth formula is a closed 33-primitive macro
at source ordinal interval [161,194). The first and second proposals
replace it by a left-associated composition

    ((push(first),push(second)),membership_constructor).

The third uses the right-associated composition

    (push(c),(push(a),membership_constructor)).

Each push has 26 primitive occurrences, and the membership constructor
has 28. Thus the replacement has 80 occurrences and raises the whole
program's primitive count by 47. All three constituents have the
inherited closed stack contracts. Their concatenation leaves the
membership code R(first,second) on the stack and preserves the
input registers and scratch invariants. Both associations therefore
have the same register-machine semantics.

Apply the exact four K219 equality-macro replacements after making
this substitution in K220. The resulting sources are:

| Fourth formula | Source artifact | DAG nodes | Primitive occurrences | Depth | Maximum zero run |
|---|---|---:|---:|---:|---:|
| R(a,b) | `conditional_membership/ab_left/sites.json` | 205 | 4791 | 38 | 6 |
| R(b,c) | `conditional_membership/bc_left/sites.json` | 205 | 4791 | 38 | 6 |
| R(c,a) | `conditional_membership/ca_right/sites.json` | 205 | 4791 | 38 | 6 |

For comparison, the exact K219 source has 206 DAG nodes and 4,744
primitive occurrences. The other nine tested ordered-pair and
association variants had larger DAGs. Independent arithmetic and
interval control-flow graph constructors agreed on all twelve source
variants. The inherited incremental native compiler rejected each
of these direct candidates with `Decoder prefix changed or did not
advance`; these measurements by themselves are not a verified native
218-state construction.

The reproducer is `calculus_experiments/compose_membership219.py`, using
`calculus_experiments/rho8_membership.py` and the pinned inherited source tools. Its full
results are `conditional_membership/summary.json`.

## Proven direction and exact missing theorem

For each proposal, every new propositional axiom is literally an
instance of the original unrestricted L schema. Every other axiom and
rule is retained. Consequently every proof in the changed calculus is
already a proof in the original one (with the appropriate fourth
input supplied to the original AX command). This gives the formalizable
direction

\[
\operatorname{Con}(\mathrm{ZFC})
\ \Longrightarrow\ \operatorname{Con}(T_{ab}),
\quad
\operatorname{Con}(\mathrm{ZFC})
\ \Longrightarrow\ \operatorname{Con}(T_{bc}),
\quad
\operatorname{Con}(\mathrm{ZFC})
\ \Longrightarrow\ \operatorname{Con}(T_{ca}).
\]

The converses have **not** been proved. In particular, a native machine
correctly compiling one of these sources would satisfy the target
equivalence only after a lower consistency-strength proof for that
specific changed calculus. A smaller source DAG does not discharge
this obligation.

A sufficient missing theorem would be a primitive recursive derivation
of every unrestricted L(A,B,C,U) from the retained rows and the
restricted row of the chosen proposal. A weaker sufficient result
would be a finite-proof interpretation of the inherited ordinary
first-order support-bearing K theory into the changed calculus. Full
theorem-set equivalence is not required, but one of these lower-strength
arguments, or an equally strong alternative, is required.

## Why these proposals escape one known obstruction

The full HC countermodel for the previous fourth-input restrictions
uses designated value 3 and implication matrix

\[
\begin{pmatrix}
3&3&3&3\\
3&3&1&3\\
3&3&3&3\\
0&0&0&3
\end{pmatrix}.
\]

Its only falsifying L valuations are
(A,B,C,U)=(0,3,1,2) and (1,3,1,2). Every implication-headed,
quantifier-headed or equality-headed expression avoids value 2, so
restricting U to any such expression leaves that full countermodel
intact. Membership atoms can take value 2, and the obstruction therefore
does not apply to the three proposals above.

For the first proposal there is even a simple witness that the old HC
model does not validate its restricted row. Set a=1 and b=0, so A is
native falsum and B is truth; choose c=R(2,3)=73. The formula C uses
variable labels 2 and 3, while U=R(1,0) uses labels 1 and 0. The old
HC coloring permits these disjoint pairs to receive values 1 and 2
respectively, producing the first falsifying valuation. This rejects
that *particular* countermodel. It is not a completeness proof, a
consistency-strength proof, or evidence that no different countermodel
exists.

## Circular arguments that remain invalid

It is tempting to say that every formula can be named by a fresh
membership atom using separation, then substitute this atom in place
of U. The inherited derivation of separation and of the requisite
biconditional manipulations uses full propositional logic. It therefore
cannot be used unchanged to bootstrap that same logic in these
restricted calculi.

Similarly, uniform substitution of formulas for relation atoms is not
a primitive rule of the native calculus. Alpha-renaming a formula
changes its raw code and hence changes the variable labels appearing
in its next restricted propositional instance. A proof of admissible
renaming or a definitional-extension theorem must address this code
dependence explicitly. The elementary fact that a is larger than every
label in decoded A supplies useful freshness, but does not by itself
justify either substitution step.

These three sources are therefore research artifacts with status
`LOGICAL_CALIBRATION_OPEN`, not solutions to the requested calibrated
machine problem.
