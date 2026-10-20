# A three-value obstruction to K plus membership-fourth rho8

This is an ordinary finite-algebra proof about the exact numerical calculus. It is not a proof-assistant result. It proves more than failure of a bounded proof search: the proposed K extension has an elementary consistency proof. Adding every quantified double-negation-elimination instance does not remove the obstruction.

## 1. Exact calculus

Use the native constructors

`I(A,B)=4P(A,B)`, `R(i,j)=4P(i,j)+1`, `Q_i(A)=4P(i,A)+2`, `E(i,j)=4P(i,j)+3`,

where `P(x,y)=(x+y)(x+y+1)/2+y`. Truth is numerical code 0; falsum is numerical code 1=`R(0,0)`. Define `N A=I(A,1)` and `Ex_i A=N(Q_i(N A))`.

Retain truth, MP, theorem-only GEN, rho1–6, merged G, and the literal `bundle222(a,b,c)` with gate `c≠a,b`, exactly as in the pinned Code254/KCode222 snapshots. Replace unrestricted rho8 by

`H(A,B,C)=I(I(I(C,R(A,B)),A), I(I(A,C),I(B,C)))`.

Add all K instances `I(A,I(B,A))`. The following model also validates all additional QS instances `I(N(N(Q_i A)),Q_i A)`.

The private label and matrix in the bundle remain the *same numerical code c*. The argument below uses that coupling and makes no change to the bundle.

## 2. Algebra and all-natural valuation

Take carrier `{0,1,2}`, designated set `{2}`, truth value `t=2`, and falsum value `f=0`. Distinguish these carrier values from numerical formula codes.

The implication and membership operations, with first argument indexing rows, are:

| J | 0 | 1 | 2 |
|---|---:|---:|---:|
| 0 | 1 | 2 | 2 |
| 1 | 2 | 2 | 2 |
| 2 | 1 | 1 | 2 |

| r | 0 | 1 | 2 |
|---|---:|---:|---:|
| 0 | 1 | 0 | 2 |
| 1 | 1 | 0 | 2 |
| 2 | 1 | 0 | 0 |

Equality has constant value 0. The quantifier operation ignores its first argument and uses `q(0)=1, q(1)=1, q(2)=2` on its matrix value.

Define `v(0)=2`. For positive n, unpair `floor(n/4)` as `(x,y)` and use the tag:

- tag 0: `v(n)=J(v(x),v(y))`;
- tag 1: `v(n)=r(v(x),v(y))`;
- tag 2: `v(n)=q(v(y))`;
- tag 3: `v(n)=0`.

Both x and y are at most `floor(n/4)<n`, so course-of-values recursion defines v for *every* natural code. This is primitive recursive by building the finite list of preceding values. For positive constructor outputs the constructor equations follow immediately. The only zero-output constructor case is `I(0,0)=0`; its equation holds because `J(2,2)=2`. Also `v(1)=r(v(0),v(0))=r(2,2)=0`, as required for native falsum.

Thus, in particular,

`v(R(A,B))=r(v(A),v(B))`

for arbitrary natural A,B. The membership atoms are **not constant**. Their label arguments are evaluated recursively as numerical codes. This is an algebraic valuation of the native derivability relation, not an ordinary interpretation of free variables in a Tarski structure. No admissibility of formula substitution or variable renaming is used.

All three values occur: `v(1)=0`, `v(16)=1` because 16=`I(1,1)`, and `v(0)=2`.

## 3. Truth, MP, GEN and retained rows

Truth is designated. The only designated antecedent value is 2, and `J(2,b)=2` implies b=2; therefore MP preserves designation. Since q(2)=2, theorem-only GEN preserves designation for every natural label.

Let `n(x)=J(x,0)`. Then `n=(1,2,1)`, while q fixes 1 and 2. Every implication value is either 1 or 2.

- **rho1:** equality has value 0, so `n(q(n(0)))=n(q(1))=n(1)=2`.
- **rho2:** `q(J(b,c))=J(b,c)`. The consequent `J(q(b),q(c))` can be 1 only when b=2 and c≠2, in which case the antecedent `J(b,c)` is also 1. Otherwise the consequent is 2. Both cases make the outer implication 2.
- **rho3/rho5:** their equality antecedent is 0 and their implication consequent lies in `{1,2}`; `J(0,1)=J(0,2)=2`.
- **rho4:** q is idempotent, and both iterated-quantifier values agree in `{1,2}`; the two relevant diagonal implications are designated.
- **rho6:** if b=2, `Ex(Q b)` has value 2, so the row is `J(2,2)=2`. If b∈{0,1}, `Ex(Q b)` has value 1, and `J(1,b)=2`.
- **G:** the two equality antecedents are 0; the quantified equality has value q(0)=1. Hence the row has value `J(0,J(0,1))=2`, independently of its dependent private label `R(a,b)`.
- **K:** its inner implication is 1 only in cases where its outer antecedent a is 0 or 1; then `J(a,1)=2`. If the inner implication is 2, the outer result is always 2.

These calculations cover all natural instances by the constructor equations. The separate executable finite checker evaluates 9 or 27 value assignments for each row and obtains only value 2.

## 4. Exact restricted rho8

For the displayed J, the unrestricted four-value-input expression

`J(J(J(c,u),a), J(J(a,c),J(b,c)))`

is undesignated exactly at `(a,b,c,u)=(1,0,0,0)` and `(1,2,0,0)`. This is an 81-case finite fact, independently checked in the certificate.

For the restricted row, these cases cannot occur: `r(1,0)=1` and `r(1,2)=2`, whereas failure requires u=0. Therefore every exact `H(A,B,C)` is designated. This argument respects the dependence of the fourth parameter on the very same natural A and B.

## 5. The full literal seed bundle

Use the actual expanded definitions, with scalar values a,b,c denoting the values of their numerical parameters:

- `Sub(a,b;k)=Q_k(I(R(k,a),R(k,b)))`;
- `req(b,k,m)=Q_b(I(m,N(Q_b(I(m,N(R(b,k)))))))`;
- `clos(a,b,k,m)=Q_b(I(R(b,k),N(Q_a(I(m,N(Q_a(I(Sub(a,b;k),req(b,k,m)))))))))`;
- `nks(a,b,c)=Q_c(I(clos(a,b,c,c),N(req(b,c,c))))`;
- `V(a,b,c)=I(R(a,b),Q_c(R(a,b)))`;
- `bundle222(a,b,c)=N(I(V(a,b,c),nks(a,b,c)))`.

For every a,b,c in the carrier, `req(b,c,c)=2`. If c≠2, the outer matrix antecedent c is 0 or 1 and its consequent is a nonzero negation value, so its implication is 2. If c=2, membership `r(b,c)` is 0 or 2, and direct evaluation in those two cases again gives 2. The excluded combination c=2 with membership value 1 is precisely where the literal matrix/private-label coupling matters.

Now `Sub` lies in `{1,2}`. Since `req=2`, its implication to `req` is 2. The inner quantified value is 2, whose negation is 1. If c=2, the remaining inner negation becomes 2, so the outer implication is 2. If c is 0 or 1, that remaining negation is 1, while `r(b,c)` is respectively 1 or 0, and both `J(1,1)` and `J(0,1)` equal 2. Thus `clos(a,b,c,c)=2` in every case.

Consequently `nks=q(J(2,n(2)))=q(J(2,1))=1`. Independently, `V=J(r,q(r))=2` for each possible membership value r. The literal bundle therefore has value `n(J(2,1))=n(1)=2`.

All 27 value triples validate the complete bundle without a gate assumption. Therefore every actually emitted gated instance validates. This is a stronger soundness check; **no ungated axiom is introduced into the calculus**. Arbitrarily separating the matrix m from its private label k would invalidate the displayed argument and is not claimed.

## 6. Quantified stability and nonderivability witnesses

Every quantified formula has value 1 or 2. Double negation fixes both values, and `J(1,1)=J(2,2)=2`. Hence all QS instances are designated as well.

Nevertheless, the formula `F→F` has numerical code 16 and value 1, so it is not derivable. Thus arbitrary identity and EFQ are not available. In particular a general deduction theorem fails: a derivation of F from temporary hypothesis F cannot always be discharged to `F→F` in this system.

The internalized composition schema `(B→C)→((A→B)→(A→C))` and S both fail at carrier `(a,b,c)=(0,1,0)`, realized by natural parameters `(1,16,1)`. The missing composition in the K+rho6 explosion argument is therefore a real algebraic obstruction, not merely a limitation of the earlier search. Full DNE fails at A=F.

The matrix also validates the previously derived five-node theorem `(T→C)→(B→C)`. It cannot be used to derive arbitrary composition.

## 7. Consistency and calibration consequence

Induction on any finite derivation preserves value 2: the cases are truth, the exact validated rows, the gated bundle, K, optionally QS, MP and theorem-only GEN. Since the native falsum has value 0, no such derivation ends in F.

The finite tables, pairing bounds, primitive-recursive valuation, constructor laws and finite-proof induction can be formalized in PA. They establish the usual arithmetized consistency of this modified calculus. This is an ordinary formalizability claim, not a newly checked Lean or Rocq theorem.

Consequently, assuming ZFC is consistent, there is no ZFC-provable implication from this calculus's consistency to the usual Con(ZFC): combining such an implication with the elementary consistency proof would make ZFC prove its own consistency. This is the standard conditional second-incompleteness consequence. It does not assert an unconditional inequality between the standard truth values of the two consistency sentences.

K alone, even supplemented with QS, therefore cannot repair the membership-fourth proposal in the requested formal-calibration sense. Adding S, composition, identity or another schema that fails this model escapes this particular obstruction; no calibration of those further systems is asserted. The earlier K/S+QS calibration is unaffected because its S schema fails here.

## 8. Evidence and limitations

`search.cpp` found this candidate after 26,846 bounded heuristic proposal iterations, in approximately 0.03 seconds. Discovery speed and unsuccessful earlier searches have no role in the proof. `check_model.py` is a separately written literal-constructor evaluator; it imports no search code and checks all row assignments, the exact bundle, preservation, concrete failing schema instances, and finite code-regression controls. The all-natural conclusion follows from sections 2 and 7, not from those finite code regressions.

Exact source definitions and the first found model are retained without alteration. No source compiler, machine allocation, Lean or Rocq was run. There is no machine-state saving claim.
