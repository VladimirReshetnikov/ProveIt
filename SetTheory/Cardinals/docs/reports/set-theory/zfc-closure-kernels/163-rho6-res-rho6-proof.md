# Ordinary proof of the rho6 sampler permutation

This note proves the new source-level change in `machine/sites216.json`. The 216-state physical construction and its partial-selector saving are inherited from the accepted upstream K216. The present change is a different, explicitly checked sampler of the same universal rho6 axiom schema. It changes two transition rows while retaining 216 working states. It does not assert a new state saving beyond upstream K216.

## 1. Exact change and numerical convention

Write Cantor pairing as

\[
P(x,y)=\frac{(x+y)(x+y+1)}2+y,
\qquad I(x,y)=4P(x,y),\qquad Q_a x=4P(a,x)+2.
\]

The numerical truth and falsity codes remain 0 and 1. Put

\[
N(x)=I(x,1),\qquad
\rho_6(a,x)=I\bigl(N(Q_a N(Q_a x)),x\bigr).
\]

Thus rho6 is the retained existential-universal row `Ex_a(Q_a x) -> x`, with `Ex_a y = N(Q_a N(y))`. No dual-rho6 replacement, formula decoding convention, or renaming rule for arbitrary derived formulas is being introduced.

The logical register order is

```
0=np, 1=tw, 2=ws, 3=ac, 4=p1, 5=p2, 6=s1, 7=s2, 8=pl.
```

At the row-generation stage of AX, registers 3, 4, and 5 hold the parameters C, A, and B respectively. The original half-open ordinal interval `[902,1185)` generates `rho6(A,C)`. Apply the register permutation `(3 5)` to every CI or CD instruction in precisely this interval. In fact only four operands change:

| Ordinal | Old operation | New operation |
|---:|---|---|
| 973 | CD3 | CD5 |
| 978 | CI3 | CI5 |
| 1151 | CD3 | CD5 |
| 1156 | CI3 | CI5 |

Every source path, operation kind, other operand, and control-flow successor is retained. The interval has only one external entry, ordinal 902, and only one external exit, ordinal 1185. The independent checker resolves all 6,175 guarded edges twice: once by ancestor intervals, and once by binary program-counter arithmetic. It verifies all four changes and this entry/exit condition directly.

The corresponding native transition changes are exactly

```
199 1 1 R 166    ->    199 1 1 R 12
206 0 0 R 186    ->    206 0 0 R 76.
```

The complete physical implementation is established by the separate 6,176-case quantified primitive-runtime certificate. Source operand substitution alone would not establish these binary transition changes as a correct compiler output.

## 2. An all-natural local simulation

Let pi exchange register coordinates 3 and 5 and fix the other seven coordinates. An increment or guarded decrement of register j on a store v corresponds exactly to the same instruction on register pi(j) on store pi(v). In the decrement case the guard is preserved because `v[j] = pi(v)[pi(j)]`. CB, CC, and halt do not inspect or modify any register, and the interval's control targets are unchanged.

Consequently the original and transformed local executions satisfy the following step-by-step statement: corresponding configurations have the same primitive ordinal and stores related by pi. This holds for every natural-valued store, not merely for sampled small values or stores observed during initialization. Induction on a finite original execution proves correspondence of its complete output store. Since pi is an involution, the converse correspondence follows by the same argument.

For clarity, the original interval has the macro word

```
a a c Q N Q N c I
```

where `a`, `b`, and `c` push the old top and load A, B, and C respectively, preserving the loaded parameter; Q and I construct the numerical quantifier and implication, and N constructs numerical negation. Starting with top T and stack W, these macros construct, in order,

```
Q_A C,
N(Q_A C),
Q_A N(Q_A C),
N(Q_A N(Q_A C)),
rho6(A,C).
```

The final stack is `P(T,W)`. Registers `np,ac,p1,p2,pl` are preserved and the two scratch registers are again zero. These are the inherited all-natural load and constructor contracts. The transformed word is

```
a a b Q N Q N b I.
```

The register-permutation simulation therefore gives its exact contract:

\[
(np,T,W,C,A,B,0,0,pl)
\longmapsto
(np,\rho_6(A,B),P(T,W),C,A,B,0,0,pl).
\]

Both C and B are preserved. No other emitted row or the subsequent gated bundle sees a modified parameter. The interval terminates normally on every clean input because the original loads and constructors do, and the permutation preserves that finite execution.

This is a local simulation and a changed macro contract. It is not an assertion that the two complete source programs have identical register stores at corresponding ordinals: their generated rho6 entries generally differ.

## 3. The exact AX interface and the ten entries

Retain the command-root tuple `(t,w,d,h)`. For an AX command with wire fields `[c+3,z,y,x]`, the numerical parameters are

\[
U=d+z,\qquad A=U+x,\qquad B=h+y,\qquad C=c.
\]

The generated quantifier is still `Q_U h`, where h is the incoming cache, before y is added to form B. Write `K(A,B,C)` for the literal gated bundle value. It is zero when `C=A` or `C=B`, and otherwise is the exact inherited bundle with its private code/label coupling.

Write `R_1,...,R_5` for the unchanged first five rows, `G_eq` for the merged equality row, and L for the dominated rho8 row. In the new program AX has the exact output

\[
(t',w',d',h')=(K(A,B,C),w',0,0),
\]

with

\[
w'=[R_1,R_2,R_3,R_4,R_5,\rho_6(A,B),G_{eq},L,Q_Uh,t;w].
\]

Bracket notation means right-nested P, with the leftmost item next to be popped. There are exactly ten pushed entries: eight row instances, the generalized incoming cache, and the saved old top. The only changed entry is the sixth. In particular the row position, total batch length, and cleanup counts are retained.

Every new sixth entry is an instance of the same universally quantified numerical axiom schema. The natural parameters A and B need not decode to formulas for this statement: the inherited calculus admits all natural instances. The other rows, restricted rho8 condition `U<=A`, theorem-only GEN, and the literal bundle are unchanged. Therefore the original theoremhood invariant for top, cache, and stack survives every command of the new program.

## 4. An explicit rho6 compiler block

Completeness must show that every intended pair `(a,b)` can be supplied to the new sixth slot. It is not enough to note that A and B have names of arbitrary parameters, because raw commands compute `A=d+z+x` and `B=h+y`.

Use the inherited reset/discard block

\[
D_0=[MP(1),AX(1,0,0,0)]\,NIP(0)^{10}.
\]

From every `(t,w,0,0)` it returns `(0,w,0,0)`. Its proof still holds after the sampler change. MP fails against its zero cache because `I(t,1)>0`, leaving a saved top of zero. In the following AX, `U=A=C=1`, so the gated top is zero. The nine generated entries remain nonfalsity codes: the axiom rows are implication codes, hence divisible by four, and the generalized code is congruent to two modulo four. The changed sixth entry `rho6(1,0)` has the same nonfalsity property as its predecessor. Ten NIPs remove the batch and restore zero cache without examining the protected underlying stack.

For any natural a and b, define

\[
B_{\rho_6(a,b)}
=D_0\;[AX(a,0,b,a)]\;NIP(0)^6\;[DROP(0)]\;NIP(0)^5.
\]

The AX wire fields are exactly

```
[a+3, 0, b, a].
```

After D0, its input has `d=h=0`. Thus it computes

\[
U=0,\quad A=a,\quad B=b,\quad C=a.
\]

The dominated condition `U<=A` is automatic, and the gate is closed because `C=A`; hence the top produced by AX is zero. Let `S_1,...,S_5` denote its first five unchanged rows, write `R=rho6(a,b)`, and abbreviate the remaining three generated entries as `G,L,Q`. The command states are exactly

\[
\begin{aligned}
(0,w,0,0)
&\longmapsto (0,[S_1,\ldots,S_5,R,G,L,Q,0;w],0,0)\\
&\longmapsto (0,[G,L,Q,0;w],0,R) &&\text{after six NIPs}\\
&\longmapsto (R,[0,G,L,Q,0;w],0,R) &&\text{after DROP}\\
&\longmapsto (R,w,0,0) &&\text{after five NIPs}.
\end{aligned}
\]

All examined caches in this calculation are nonfalsity codes: implication codes are divisible by four, Q has residue two, and the inserted zeros are truth. Thus this particular axiom block returns normally, with the exact strong contract shown, for every a, b, t and arbitrary finite stack code w. No assumption that w is a sound theorem stack is needed for the strong contract, because the block does not inspect it.

The other axiom-row blocks still select their original slots. Their unused sixth entry may change, but it remains a sound, nonfalsity axiom and the batch still has ten entries. The gated-bundle block and the strong MP and GEN compilers therefore keep their original selection and cleanup counts. Wherever an inherited compiler permits early halt upon encountering an already derived falsum, the same sound early-halt convention applies. Reset padding still supplies refutation programs above every finite candidate cutoff, since D0 remains a reset block with the same command encoding.

This establishes completeness of the new sampler for the full retained numerical calculus. It does so by supplying free parameters separately to an axiom instance. It does not invoke an unproved operation that renames labels inside an arbitrary derived theorem or inside the literal bundle.

## 5. Composition with the exact binary machine

The inherited ordinary calibration identifies falsum derivability in the dominated numerical calculus with the existence of a finite ZFC refutation. Soundness from Section 3 and the compiler from Section 4 identify that same event with halting of the new source search from the calibrated root seed.

The fresh universal runtime check for the exact new table establishes all 6,176 primitive cases over independently arbitrary natural registers and gap, and an arbitrary nonempty finite spare list. It reports 1,711,040 symbolic rules, coverage of all 432 rows, and positive affine durations with minimum constant 13. These universally quantified contracts, rather than finite test execution, implement the source computation on the binary machine.

The independent blank audit starts in state 0 on an all-zero two-way tape. After exactly 313,133 transitions, both the sparse native interpreter and the separately parsed dense canonical interpreter have the identical complete execution trace up to state renaming and the following complete endpoint:

```
state 84; head -5; root control address;
gap 80;
logical registers [3,0,0,0,3,0,0,0,0];
130 spare registers, each equal to 1;
277 one-cells in total; zero everywhere else.
```

Neither of the two changed native rows occurs in that prefix, which also proves that its entire blank initialization is inherited unchanged from the pinned upstream table. The canonicalization is a bijection of all 216 working states plus halt, checked against all 432 rows. The row identity under this bijection proves equivalence of the native and canonical presentations on every initial tape by induction on steps; the blank simulation is a separate endpoint check.

All source reasoning, finite encodings, local simulations, compiler constructions, and unary/list inductions used here are ordinary mathematics formalizable in ZFC. Combining them yields

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M_{216}^{\rho_6},\mathrm{blank})
\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The equivalence does not assume Con(ZFC), assert unconditional nonhalting, assert minimality, or claim a new exact-table Lean/Rocq certificate. The present contribution is the rigorously composed alternative rho6 sampler and its checked 216-state table; the state-saving partial-selector construction retains its upstream attribution.
