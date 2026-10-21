# R(A,B) fourth parameter: a broader conditional extraction theorem

This is a further **conditional semantic theorem**, not the missing
consistency calibration and not a new machine. It applies to the proposal
in upstream commit `adfaaaec`, which replaces rho8 by

```
L(A,B,C,R(A,B)) = ((C -> R(A,B)) -> A) ->
                  ((A -> C) -> (B -> C)).
```

The new observation removes the need for a single designated value and
for the extra implication laws assumed in `fresh-label.md`. Boolean
negation and the stipulated quantifier semantics remain substantive
model-existence assumptions.

## Hypotheses

Let V be a value set with an arbitrary designated subset D. Choose
`t in D` and `0 not in D`. Interpret implication by a fixed operation I
and membership by a uniform relation `r:X×X -> V` on a nonempty domain.
Assume the following.

1. Modus ponens preserves designation: `x in D` and `I(x,y) in D`
   imply `y in D`.
2. Relative negation is Boolean: `I(x,0)=0` for `x in D`, and
   `I(x,0)=t` for `x not in D`.
3. Quantification is designated exactly when every corresponding
   coordinate variant has a designated body. Its actual output need
   not be Boolean or constant among designated values.
4. Native evaluation is compositional, code zero has value t, and its
   implication alias gives `I(t,t)=t`.
5. Membership is irreflexive, `r(x,x)=0`. Native formulas have their
   strict free-label support bound.
6. Every modified rho8 instance, every original rho6 instance, and every
   enabled native seed/vacuity bundle is valid at every assignment.
7. If the ordinary target matrices include equality, the native equality
   atom is designated exactly when its two assigned objects are identical.
   Its value need not itself be Boolean, because the translation below
   normalizes atoms by double negation.

The first six hypotheses suffice for the membership-only matrix language.
The seventh states explicitly the equality interpretation used when
extracting all ordinary first-order matrices. An alternative already
justified equality-eliminating interpretation can be used instead; no
new equality interpretation is proved here.

Only realized native values are used in the argument. Assuming the stated
operation laws on all V is a convenient stronger formulation.

## 1. A literal four-code instance forces falsum to imply truth

Put `q=I(0,t)`. This is the value of native formula code
`B=I(F,0)=4`. Use the literal row

```
A=0, B=4, C=1, U=R(0,4)=57.
```

Assign labels 0 and 4 the same domain element. U is then 0; B remains q
because its only possible coordinate dependence is through the diagonal
falsum R(0,0). Suppose q were nondesignated. Boolean negation gives

```
I(0,0)=t,  I(t,0)=0,  I(q,0)=t.
```

The entire row evaluates to

```
I(I(I(0,0),t), I(I(t,0),I(q,0)))
  = I(t,I(0,t)) = I(t,q).
```

The row is designated and t is designated, so MP makes q designated,
a contradiction. Therefore `I(0,t) in D`. No prior ex-falso law or
single designated value was used.

## 2. Rho6 supplies the truth-antecedent law

Let a native formula A have value x at an assignment. Choose a label i
fresh from A, using its code or a larger label. A has the same value x at
every i-variant. If x is designated, every `Q_i A` is designated and
every `N Q_i A` has value 0; consequently `Ex_i Q_i A` has value t.
If x is nondesignated, every `N Q_i A` has value t, and
`Ex_i Q_i A` has value 0. The valid rho6 instance therefore gives

```
x in D     implies I(t,x) in D,
x not in D implies I(0,x) in D.
```

MP gives the reverse half of the first statement. Thus, on every realized
value, `I(t,x) in D` iff `x in D`. This was an assumption in the earlier
conditional model class; here it follows from rho6 and the stated
negation/quantifier semantics.

## 3. Every realized value implies truth

For a positive formula code B, change assignment B to the value at label
0. The strict support bound preserves B's value b and makes R(0,B)=0.
The modified row with A=C=truth becomes

```
I(q, I(t, I(b,t))) in D,
```

where q=I(0,t) is designated by step 1. Two MP applications give
`I(b,t) in D`. The code-zero case follows from I(t,t)=t.

## 4. Implication into every designated consequent is designated

Take any realized values b,c at the same assignment, with c designated.
Use the modified row whose A is truth and whose B,C are these formula
codes; write u for its fourth atom's value. Its first antecedent is
`I(I(c,u),t)`, which is designated by step 3, since I(c,u) is itself a
realized formula value. MP therefore gives

```
I(I(t,c),I(b,c)) in D.
```

Step 2 gives I(t,c) designated. Another MP gives I(b,c) designated.
This also extends ex falso to designated consequent values; together
with step 2, `I(0,x)` is designated for every realized x.

## 5. Atomic implication has material designatedness

The fixed instance A=1, B=0, C=73=R(2,3), U=5=R(1,0) realizes any two
atomic membership values c,u independently. Suppose c is nondesignated
and I(c,u) is nondesignated. Its first antecedent is then
`I(I(c,u),0)=t`. Step 2 makes I(0,c) designated, while MP prevents
I(t,c) from being designated. A designated antecedent cannot imply a
nondesignated consequent by MP, so

```
I(I(0,c),I(t,c))
```

is nondesignated. The outer row consequently violates MP with its first
antecedent t, a contradiction. Therefore I(c,u) is designated whenever
c is a nondesignated atomic value. When u is designated, step 4 covers
all c. When c is designated and u is not, MP forbids designation.
Thus, between atomic membership values,

```
I(c,u) in D  iff  c not in D or u in D.
```

The native Sub formula therefore expresses ordinary inclusion for the
relation `r*(x,y)` iff `r(x,y) in D`.

## 6. The unchanged K extraction follows

Negation is Boolean by hypothesis. Double negation is the Boolean
indicator of designation. Implication into a Boolean consequent has
material designatedness: this is Boolean negation for consequent 0,
and step 3 for consequent t. Relative conjunction and existential
quantification have their usual designatedness meanings.

Here is the literal native decomposition, with distinct public labels
a,b, private label c, and matrix chi whose actual native code is c:

```
r = R(b,c)
s = Q_c (R(c,a) -> R(c,b))
w = Q_b (chi -> N Q_b (chi -> N r))
u = Q_a (s -> w)
h = Q_b (r -> N Q_a (chi -> N u))
Dcore = Q_c (h -> N w)
bundle = N (V -> Dcore).
```

The Q_c inside s shadows the private container only inside s. The two
Q_a binders in h intentionally shadow one another. The matrix is
independent of c by its strict support bound. These are precisely the
native nks222 and bundle formulas; chi is not a new independent row
parameter.

For the literal bundle, designation implies Dcore is nondesignated.
Otherwise step 4 would make I(V,Dcore) designated. There is therefore
a container assignment where I(h,N w) is nondesignated. Its Boolean
consequent forces h and w both designated. At this container, w says
that whenever chi at the current input has a witness, it has a witness
belonging to the container. This follows because the inner implication
has Boolean consequent N r: its failure means both chi and r designated.

For any designated member y of the container, h and MP make
`N Q_a(chi -> N u)` designated. There is a supporting a-assignment
where `chi -> N u` is nondesignated. Its Boolean consequent makes
both chi and u designated. The inner Q_a in u ranges afresh over every
input x'. Whenever x' is a subset of y in r*, s is designated by step 5;
u and MP then make the corresponding w designated. Thus each member
has a supporting input satisfying chi, and every subset of that member
has its matrix request satisfied in the container. Together with w at
the original input, this is the full ordinary seed-K support and subset
closure condition. Only one-way extraction of h is needed; no projection
of V is used.

To realize arbitrary ordinary matrices, translate atoms by NN and put
NN around **every implication and every quantifier**. This additional
normalization of implication is needed because I(0,t) may be a designated
value other than t. Every translated subformula is then Boolean and has
the correct ordinary truth value. Recompute the actual native code of
the translated matrix and choose it as the private binder. Repeated
double-negation padding preserves its Boolean value while increasing
its code, so the private label can be made distinct from both public
labels; its own free-label support bound supplies matrix independence.
The extracted relation
r* is irreflexive and satisfies the full ordinary seed-K scheme.

## What remains open

This theorem substantially enlarges the conditional model class, but
does not show that consistency of the modified native calculus yields
such a model. In particular, a generic Lindenbaum construction does not
automatically give Boolean relative negation or the stipulated
designation semantics of all quantifiers. Those remaining properties
must be proved, or replaced by a syntactic bridge, before concluding
equiconsistency. The bounded condensed-detachment searches performed
alongside this note provide no impossibility result and no replacement
for that missing proof.
