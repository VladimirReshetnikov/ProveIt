# Exact independent-pivot equivalence and register contract

Let native falsity be `F=R(0,0)=1`, `N A = A→F`, and
`Ex_i A = N(Q_i(N A))`. All labels and formula codes below range over
arbitrary natural numbers. There is no implicit well-formedness restriction
on an externally supplied natural code, nor an assumption that different
labels denote different objects.

We use the existing all-native-code relative classical bridge from the
retained unrestricted rho8 and rho6, together with MP and closed-theorem
GEN. This justifies classical tautological inference, including
contraposition and double-negation elimination. Its proof is an inherited
dependency, not a conclusion of the new Python checker. The other retained
axioms used here are:

```
rho1(i,j)   Ex_i E(i,j)
rho2(i,A,B) Q_i(A→B) → (Q_i A → Q_i B)
rho6(i,A)   Ex_i(Q_i A) → A
G(a,b,u)    E(u,a) → (E(u,b) → Q_kappa(a,b) E(a,b))
```

K219 has `kappa(a,b)=R(a,b)` as its literal numerical binder builder. The
proof below does not change that builder. The G row is ungated.

## Retained logical facts

From a theorem `A→B`, GEN and rho2 give `Q_i A→Q_i B`. Applying this to
the contraposition `N B→N A` and contraposing again gives
`Ex_i A→Ex_i B`. The theorem

`Q_i(A→B) → (Ex_i A → Ex_i B)`

follows by lifting `(A→B)→(N B→N A)` and applying rho2 to `N B,N A`.
These use GEN only on theorems, never on an undischarged local assumption.

Apply the last theorem to `E(i,i),A`. Lifting the tautology
`A→(E(i,i)→A)` and using rho1(i,i) yields seriality
`Q_i A→Ex_i A`. Substituting `Q_i A` for A and then using rho6 gives

`Q_i Q_i A → A`.                                                    (1)

Next fix x, put `z=kappa(x,x)` and `e=E(x,x)`. Contract G(x,x,z) to
`E(z,x)→Q_z e`. Existential monotonicity, rho1(z,x), and rho6(z,e)
yield e. Thus primitive equality reflexivity is available without using
rho5, membership vacuity, or any K instance. This includes the case z=x
and all numerical zero aliases.

## Recovering the old calculus

For each enabled triple `c≠a,b`, let

```
V(a,b,c)   = R(a,b) → Q_c R(a,b)
M(a,b,c,u) = E(u,a) → (R(u,b) → Q_c R(a,b)).
```

The old bundle is literally `N(I(V,D))`, where D is its unchanged native
quantified K core. Its bare K conjunct is `N D`. The new bundle is literally
`N(I(M,D))`. Classical inference projects M and `N D` from the latter.
This describes the actual code construction; it does not silently replace
the private matrix-code binder by a fresh syntactic variable.

Choose `u=a` in the new bundle. Equality reflexivity and the projected M
give V for every enabled triple. Together with the projected `N D`, V
rebuilds the exact old bundle `N(I(V,D))`.

To recover an arbitrary ungated old instance
`E(u,a)→(R(u,b)→R(a,b))`, choose the numerical label
`c=max(a,b)+1`. This always passes the gate; it need not differ from u.
The V theorem just obtained, generalized at c and distributed by rho2,
gives

`Q_c R(a,b) → Q_c Q_c R(a,b)`.

Composing with (1) eliminates the quantifier. The M instance with the
original independent pivot u then gives precisely the required rho5.
No universal instantiation rule, semantic equality principle, or freshness
of c inside an arbitrary matrix has been used.

Conversely, old rho5 followed by old V gives M for every enabled triple
and every u. Projecting `N D` from the old bundle rebuilds the new bundle.
All other rows are literally retained, and the replaced rho5 output slot
is native truth code 0. Disabled bundle instances still output truth code
0 under the unchanged gate. Truth is already a theorem in either calculus.

These are uniform finite proof replacements in both directions. In a
derivation, replace each changed axiom instance by its displayed finite
derivation and preserve MP/GEN. The conclusion is the identical numerical
formula code, so in particular code 1 is derivable in one calculus iff it
is derivable in the other. The existing ordinary ZFC calibration therefore
transfers to the **calculus**, without asserting a machine implementation.
The checker records an explicit schematic trace for both directions; each
tautology step is exhaustively checked on its propositional atoms, with
quantified formulas treated as atoms.

## All-natural storage and gate argument for the source experiment

Write `P(x,y)=(x+y)(x+y+1)/2+y`. The inherited closed source macros have
these register contracts, with logical scratch registers 6 and 7 initially
zero and zero again on exit:

* `PUSH(i,j)` sends `(r_i,r_j)` to `(0,P(r_i,r_j))`.
* `POP(j,k)` sends `(r_j,r_k)` from `(P(x,y),0)` to `(y,x)`.
* The copy macro sends `(r_i,r_j)` from `(x,0)` to `(x,x)`.
* A decrement/increment transfer sends `(r_i,r_j)` from `(x,0)` to `(0,x)`.

Their loops terminate by decreasing a natural counter. The PUSH arithmetic
is the triangular pairing identity, and POP is the inverse Cantor routine
already used by rho8's input read and implication construction. Renaming
registers preserves these contracts because the chosen scratch and input
registers remain distinct. The measure program binds the reused macros to
their exact K219 decoder subtrees, rather than supplying new arithmetic
implementations.

Immediately after the original fourth-field read, write the full state as

`[n,u,S,c,a,b,0,0,t]`.

Here n is the old cache, t is the remaining proof-data tail, and S is the
stack containing the already pushed c and older outputs. The new closed
save factor performs:

1. PUSH(0,8): `[0,u,S,c,a,b,0,0,P(n,t)]`.
2. Transfer 1→0: `[u,0,S,c,a,b,0,0,P(n,t)]`.
3. Copy 0→1: `[u,u,S,c,a,b,0,0,P(n,t)]`.

Thus the original rho8 construction sees exactly its original top and
stack. The later changed M construction reads u by copying register 0.
All other formula-construction macros leave registers 0 and 8 untouched.
They use only the original parameters and registers 1,2,6,7.

After construction, for arbitrary resulting top T and stack S', the restore
factor clears register 0, POPs register 8 into scratch 6, and transfers 6→0.
It sends

`[u,T,S',c,a,b,0,0,P(n,t)]` to `[n,T,S',c,a,b,0,0,t]`.

The source then runs the original freshness gate. Its parameters a,b,c and
all exterior registers have been restored or preserved. The argument
therefore applies to **all natural** n,u,t,a,b,c, including u equal to any
other label and either gate outcome. It introduces no positivity or
extra-freshness premise.

The rho5 slot is replaced by one original PUSH, which retains its previous
top on the stack and sets the new top to truth 0. It consequently has the
same one-output stack effect as the removed rho5 constructor. M replaces V
in the final bundle without changing that bundle's output count. The AX
stack/scheduler interface and input consumption count are unchanged.

The exact edits at original primitive half-open intervals are:

| Interval | Replacement |
| --- | --- |
| `[194,221)` | save factor followed by original first rho8 implication |
| `[1178,1474)` | original PUSH producing truth 0 |
| `[2650,2892)` | postfix M: `u a E u b R c a b R Q I I` |
| `[4536,4563)` | original final implication followed by restore factor |

Every replaced forest and new factor is closed. Closed-factor replacement
preserves the surrounding continue/break interpretation. Both independent
whole-source CFG constructions agree. These source arguments do not make
the failed binary allocation valid. Full primitive simulation and a fresh
blank startup would still be required for a machine claim.
