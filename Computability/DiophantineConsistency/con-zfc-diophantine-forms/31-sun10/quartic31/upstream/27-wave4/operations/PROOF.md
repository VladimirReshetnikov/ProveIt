> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# Low-operation positive systems from the retained quotient construction

## Result, limitations, and attribution

This note adds exact positive graph lifts to ProveIt's `22-monic12` retained
system, and separately combines that system with `19-wang943`'s auxiliary-gap
substitution. The input is pinned to repository commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. No repository code was executed.
Only the received JSON arithmetic circuit was consumed by the newly written
`build_operations.py`. The received Python scripts are inert reference files.

All operation counts charge every binary addition, subtraction, multiplication,
including multiplication by fixed numerals; a comparison between two computed
values is free. Thus these systems do not beat the 59-gate system count or the
67-gate single-polynomial count. They improve degree at the same system gate
count, at the cost of retaining more witnesses and equations. No optimality
claim is made, and no stronger unknown-count claim than the comparison below
is intended.

| Construction | Positive variables | Equations | Maximum residual degree | Gates | SOS degree | SOS gates |
|---|---:|---:|---:|---:|---:|---:|
| Source retained59 | 16 | 7 | 24 | 59 | 48 | 79 |
| Auxiliary gap | 16 | 7 | 22 | 60 | 44 | 80 |
| Retain Y | 17 | 8 | 12 | 59 | 24 | 82 |
| Retain Y,E | 18 | 9 | 10 | 59 | 20 | 85 |
| Retain Y,E,c | 19 | 10 | 8 | 59 | 16 | 88 |
| Retain Y,E,c,A0 | 20 | 11 | 6 | 59 | 12 | 91 |

The 16-variable degree-44 SOS is dominated by package 19's 15-variable,
76-gate degree-44 SOS; it is included to document the exact combination, not
as a recommended single equation. The graph lifts are useful when small
system arithmetic size and moderate degree matter together. Other source
packages optimize variable count and low degree differently.

Attribution: the retained-quotient encoding, complete compiler/Pell bridge, and
59-gate arithmetic schedule are upstream work in `22-monic12` (itself composing
09's retained quotients with 12's transport shift). The auxiliary gap and its
canonical positivity are upstream work in `19-wang943`. The graph-lift selection,
explicit generated packets, uniform monomial certificates, independent local
emitter, and comparisons here are the new synthesis. These are ordinary
mathematical reductions formalizable in ZFC, not a new Lean/Rocq formalization.

## Literal base system

The delivered circuits select the entire compact 943-tile tuple from package
19: B=2^(5^10), beta=B-1, and the K,MC,MF_source integers specified by
`upstream/COEFFICIENT_BINDING_943.json` and the bounded definitions in
`upstream/WANG943_COMPACT_LAYOUT.md`. Its K is the circuit port K0, and
MF_source is the circuit port MF. The copied coefficient-language note
supplies the ordered tile recipe and clause coefficients required by those
formulas. These exact fixed integers are not additional unknowns. The
following argument also works for any other complete authentic Start-only
compiler tuple beta,K0,MC,MF. Here beta
is B-1 and MF is the shifted source mask, not the native high mask. The entire
four-port binding must come from one proved compiler recipe. Do not mix ports.
The positive witnesses of the base system are

J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma.

All expressions below are polynomial abbreviations, not additional witnesses,
except when a specifically listed graph lift makes one a witness:

q=beta J+1, X=wq, Y=sq^3, E=XY, k=eta+zeta,
c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
D=X+ac+gamma H, C=q-F-alpha,
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
L=EkY, V=of-c, U=jc-R, I=ic^2, A0=Delta(f^2-1).

The seven polynomial equations are

1. tau^2-L(L+k)=1.
2. D^2-Delta c^2=1.
3. A0(V^2-y^2)+y^2=1.
4. k-hE-R=1.
5. (K0+w)C=F+z(q-1).
6. I^2=A0.
7. U=V.

This is the exact upstream `retained16_system59.json`. In particular z is the
shifted positive transport quotient, z_old-1. It must not be confused with the
unshifted quotient in package 19's grouped polynomials.

## The 17-variable recommendation

Promote Y to an independent strictly positive variable, delete the abbreviation
Y=sq^3, and append the polynomial equation

8. Y=sq^3.

Use this independent Y everywhere else, including in E, c, a, and L. The
resulting system is entirely polynomial and has no divisibility predicates,
root operators, rational formulas, variable exponentiation, or auxiliary
existential signs hidden in its definition. Every remaining symbol is a
polynomial expression in precisely the listed seventeen positive variables.
Its complete binary evaluator is `lift17_Y59.json`.

In the evaluator, the original gate Y=s*q3 is renamed Y_calc=s*q3. Subsequent
arithmetic uses the new input Y, and the extra equality is Y=Y_calc. There is
no extra arithmetic gate. The comparison, like all source comparisons, is free.

### Equivalence proof

Given a positive solution of the new system, equation 8 forces the new witness
to equal the original polynomial abbreviation. Substitution into equations
1-7 gives a positive solution of the upstream retained59 system. Conversely,
every positive upstream solution extends uniquely by Y=sq^3, which is positive
because s and q are positive. Thus the positive solution sets are in bijection.

The upstream retained59 theorem proves existence of a positive solution iff
blank-tape K215 halts; the calibrated K215 theorem proves halting iff a finite
syntactic ZFC refutation exists. Composing those two already-proved interfaces
with the graph bijection gives, as a theorem formalizable in ZFC,

Con(ZFC) iff there is no positive integer solution of this 17-variable system.

This equivalence neither assumes nor proves Con(ZFC). It does not claim
end-to-end proof-assistant verification of the combined Diophantine bridge.

### Exact degrees

Write Q=beta J and k=eta+zeta. For the lifted system the highest homogeneous
parts of X,E,c,a are wQ, wQY, kY, wQY respectively, of degrees 2,3,2,3.
L=EkY has degree 5. The seven source residual degrees, followed by the new
graph residual, are exactly

10, 9, 12, 4, 2, 10, 4, 4.

For the potentially deceptive main norm, use the polynomial identity

D^2-Delta c^2 = 2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

Its highest part is 8 gamma (wQY)^2(kY), of degree 9. For the auxiliary norm,
A0 has leader (wQY)^2 f^2, and V has leader of-kY. Thus its degree-12 leader is

(wQY)^2 f^2 (of-kY)^2.

For example, its monomial J^2 w^2 Y^2 o^2 f^4 has coefficient beta^2, which is
nonzero for every authentic compiler tuple. This is a uniform degree proof,
not a random numerical degree guess. The source packets additionally contain
one exact c*beta^r monomial certificate for every residual. The sum of squared
residuals therefore has degree exactly 24: over the real polynomial ring the
highest homogeneous squares cannot cancel.

## Further graph lifts

The same construction may additionally retain E, c, and A0 and append,
respectively, E=XY, c=kY+eta, A0=Delta(f^2-1). All source gates remain present
as calculated sides of the new comparisons, so every system still has exactly
59 binary gates (33 multiplications and 26 additions/subtractions).

Y,E,c are unconditionally positive on positive original witnesses. A0 is
positive on every original zero because source equation 6 gives A0=I^2 and
I=ic^2>0. Hence all the graph extensions are legitimate positive extensions,
with no assumption that f^2-1 is positive off the zero set.

The same substitution/projection bijection proves each system has exactly the
required existence-equivalence. Exact full symbolic expansion supplies the
residual degree lists and uniform monomial certificates in each JSON. Their
maxima are 10,8,6 for 18,19,20 positive variables respectively.

## The optional auxiliary gap

Replace the positive source coordinate y by a positive coordinate e and the
polynomial expression y=V+e. All other source coordinates and seven equations
stay unchanged. This adds one addition gate and lowers the auxiliary residual
from degree 24 to degree 20; the first and strong residuals still have degree
22. Thus the system has 60 gates and maximum degree 22.

For soundness, a positive tuple for the new system reconstructs an integer
source root y=V+e which need not initially be positive. But equation 6 gives
A0=I^2>1, and equation 3 would give A0 V^2=1 if y=0, impossible. Replacing y
by its positive absolute value preserves all source equations because y
occurs only through y^2. This supplies a positive source solution. No sign
assumption about V or V+e was smuggled into this argument.

For completeness use the established canonical positive Pell/compiler
witnesses, which have V>1 and A0>1 (package 19's grouped proof, section 2).
Equation 3 implies

(A0-1)(y^2-V^2)=V^2-1>0.

Hence y>V and e=y-V is a positive integer. This gives a new positive solution.
Existence equivalence is sufficient; no bijection of every noncanonical tuple
is needed for this gap substitution.

## Verification boundary

`python3 build_operations.py` regenerates the five systems and their SOS
polynomials. It verifies closure, all gate/input liveness, exact arithmetic
ledgers, full multivariate polynomial degrees treating the four compiler
ports as constants, and uniform per-residual leading monomials. For each
system it checks 160 independently computed complete residual vectors on
signed integer and rational assignments. These finite checks certify the
stated identities and metrics, not the semantic compiler or K215 theorems.
No guessed coefficient binding or actual K215 halting witness is used.

## Sources at the exact review pin

- https://github.com/VladimirReshetnikov/ProveIt/blob/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/22-monic12/data/retained16_system59.json
- https://github.com/VladimirReshetnikov/ProveIt/blob/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/22-monic12/proofs/RETAINED59_PROOF.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/19-wang943/arithmetic/GROUPED_TRADEOFF_PROOF.md
