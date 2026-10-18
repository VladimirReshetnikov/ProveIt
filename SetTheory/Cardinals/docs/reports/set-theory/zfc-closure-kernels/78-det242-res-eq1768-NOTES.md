# A 1,768-bit equational target for the ZFC consistency search

**Result.** The complete equational packet retained in ProveIt's source 70 has
2,324 bits, 21 equations, 446 term nodes, 12 signature symbols and a six-variable
capacity. This contribution gives a packet with **1,768 bits, 22 equations,
420 term nodes, 11 signature symbols and a five-variable capacity**. The decrease
is 556 bits (23.9243%). Both packets include their signature arities, variable
capacity, equation delimiters and the two ground endpoints.

This is an independent alternative to the current numerical proof-search
machine. It supplies **no binary Turing-machine state bound**. Its useful exact
claim is an ordinary ZFC proof of equivalence of the two ground-rewrite
reachability problems. It inherits the existing FC13B-to-ZFC calibration and
does not promote that calibration to a new proof-assistant result.

The reference input is pinned to ProveIt
`e58338db7545909907e07a7603e8eb88625c527a`, specifically
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`:

- `data/70-c244-equational-reference-FC13B_complete.json`;
- `data/70-c244-equational-grouped.json`;
- `code/70-c244-equational-build_equations.py`;
- `code/70-c244-equational-equational_search.py`.

The input is the 23-clause, 57-literal, equality-complete FC13B theory. Its
published source-70 packet is a separate artifact from both the current
243-state machine and the new 242-state local reduction developed elsewhere in
this investigation.

## 1. Eliminate membership using the existing assignment language

First work in the native-equality presentation underlying the explicit
completion. Write `Inc(s,a)` for incidence of assignment `s` in class `a`,
`V(s,j)` for evaluation at coordinate `j`, and `C(s,j,z)` for an update. Let

\[
  t=I(d,d),\qquad
  B(x,y)=C(C(d,d,x),t,y),\qquad
  E_*(x,y)\;\equiv\;\operatorname{Inc}(B(x,y),A(d,t)).
\]

The retained clauses say:

\[
\begin{aligned}
 V(C(s,j,z),j)&=z,\\
 k\ne j&\Longrightarrow V(C(s,j,z),k)=V(s,k),\\
 \operatorname{Inc}(s,I(a,b))&\leftrightarrow
       (\operatorname{Inc}(s,a)\to\operatorname{Inc}(s,b)),\\
 \neg\operatorname{Inc}(s,d),&\\
 \operatorname{Inc}(s,A(j,k))&\leftrightarrow E(V(s,j),V(s,k)).
\end{aligned}
\]

The implication and empty-class clauses give
`Inc(s,t)` and `not Inc(s,d)` for every `s`. Nonempty first-order domains
therefore give `d != t`. The two update laws now give

\[
 V(B(x,y),d)=x,\qquad V(B(x,y),t)=y.
\]

The atomic-incidence clause implies

\[
                 E(x,y)\leftrightarrow E_*(x,y).
\]

Replace the two atomic-incidence clauses by this definition and delete the
primitive predicate `E`. The reverse model transformation simply defines `E`
to mean `E_*`; all original native-equality axioms are recovered. Thus the
native theories are definitionally interinterpretable, with a finite proof of
the displayed equivalence available from their retained axioms.

The delivered input uses a binary predicate `Eq` in place of native equality.
Its retained reflexivity and Euclidean clauses imply that `Eq` is an equivalence
relation. Congruence is retained for every source function and for `Inc`.
The quotient therefore interprets the native-equality theory. Conversely any
native model interprets `Eq` by identity. The removed `E` congruence follows
from the retained `C` congruence, reflexivity for the fixed terms and `Inc`
congruence. A six-inference universal Horn derivation of this fact is supplied
and replayed by `verify_exact.py`.

Consequently the equality-complete source theories have the same consistency
statement in ZFC. Translating the resulting finite clauses with the inherited
Boolean backend removes one equation and changes the atomic-incidence equation.
No other `Eq` axiom or function-congruence clause is removed.

**Measured effect alone:** 21 to 20 equations; 446 to 436 term nodes;
12 to 11 signature symbols; 2,324 to 2,270 complete packet bits.

## 2. Fuse the auxiliary Boolean truth constant with the source constant

The inherited algebraization adds a NAND operation `N` and a constant `top`.
The Boolean basis is the published Sheffer law

\[
 N(N(x,N(N(y,x),x)),N(y,N(z,x)))=y,
\]

and `top = N(d,N(d,d))` designates Boolean truth. Its ground query asks whether
`N(top,top)` can be connected to `top` by instantiated contextual rewrites.

The constant `top` can be replaced everywhere by the **existing source constant
`d`**, including its definition and both endpoints. The retained defining
identity becomes

\[
                     d=N(d,N(d,d)).
\]

This forces `d` to be Boolean truth in the chosen NAND presentation. It does
not force `Inc(s,d)` to be true: the source predicates are separate operations,
and incidence need not be a Boolean evaluation of its second argument.

Here is the complete upper model argument, which also explains why this is
valid for every finite equality-free universal clause theory with a designated
constant. Given a nonempty model `M`, take the Boolean algebra `P(M)`. Choose an
injection

\[
 i:M\longrightarrow\mathcal P(M),\qquad i(d^M)=M,
\]

and a retraction `r` with `r(i(a))=a`. One explicit injection sends `d^M` to `M`
and every other element `a` to the singleton `{a}`; this works also in the
one-element case. Set `r(B)=d^M` outside the image.

Interpret each source function by

\[
 f^{\mathcal B}(B_1,\ldots,B_k)
       =i\bigl(f^M(r(B_1),\ldots,r(B_k))\bigr).
\]

Interpret each predicate operation as `M` or the empty set according to the
truth of the source predicate on the retracted arguments. Structural induction
on source terms shows that every encoded clause is satisfied. The old source
constant is now exactly Boolean truth, so the fused identity also holds.
The Boolean algebra is nontrivial because `M` is nonempty.

For the reverse direction, take any nontrivial model of the fused equations.
The Sheffer theorem supplies its Boolean-algebra structure. Choose an
ultrafilter and read a source predicate as true precisely when its Boolean
value lies in the ultrafilter. Keep the entire carrier and all original
functions. Boolean clause equations then imply the original clauses. This
construction does not quotient the Boolean carrier or assume that the source
functions preserve a Boolean congruence.

These two constructions are available inside ZFC. Together with ordinary
first-order completeness, they give the required consistency equivalence.
The ground term algebra modulo contextual rewriting gives a nontrivial model
exactly when the designated Boolean zero and one are not connected; if they
are connected, Boolean algebra collapses. This is the same ground-rewrite
completeness argument as the inherited backend.

**Measured combined effect:** membership elimination and constant fusion give
10 signature symbols plus six variable codes, exactly 16 opcodes. The old
fixed-width representation required five bits for 18 opcodes. The new one
requires four bits. This gives a complete **1,827-bit** packet. The saving
comes from crossing that encoding boundary; constant fusion alone saves only
three header bits.

## 3. Spend one variable slot on a useful ground alias

The ground subterm `I(d,d)` occurs 15 times in the 1,827-bit equations. Introduce
one constant `o` with the explicit equation

\[
                           o=I(d,d),
\]

and use `o` at all former occurrences. This is an ordinary conservative
term definition in the equational language.

To keep four-bit opcodes after adding `o`, reduce the largest axiom's variable
capacity from six to five. Replace the ternary congruence clause

\[
 Eq(x,u)\land Eq(y,v)\land Eq(z,w)
 \Longrightarrow Eq(C(x,y,z),C(u,v,w))
\]

by the two clauses

\[
\begin{aligned}
 Eq(x,u)\land Eq(y,v)&\Longrightarrow
       Eq(C(x,y,z),C(u,v,z)),\\
 Eq(z,w)&\Longrightarrow
       Eq(C(x,y,z),C(x,y,w)).
\end{aligned}
\]

The first clause uses five variables; the second uses four. The original
clause gives both using reflexivity. The two new clauses give the original
using one intermediate term `C(u,v,z)` and transitivity. Transitivity follows
from the retained reflexivity and Euclidean law. Three explicit universal Horn
proofs, totaling ten inferences, are supplied and replayed.

The two new clauses are converted to NAND equations by the inherited exact
truth-table checker, with eight and four propositional assignments respectively.
Adding the alias and replacing one congruence equation by two yields:

| Artifact | Equations | Term nodes | Symbols + variable capacity | Opcode bits | Complete bits |
| --- | ---: | ---: | ---: | ---: | ---: |
| Source 70 baseline | 21 | 446 | 12 + 6 | 5 | 2,324 |
| Membership eliminated | 20 | 436 | 11 + 6 | 5 | 2,270 |
| Truth fused only | 21 | 446 | 11 + 6 | 5 | 2,321 |
| Both changes | 20 | 436 | 10 + 6 | 4 | 1,827 |
| Both changes, alias and split congruence | 22 | 420 | 11 + 5 | 4 | **1,768** |

The final 1,768 bits comprise 49 signature/capacity bits, 1,703 equation bits
and 16 endpoint bits. There are 44 rewrite orientations. The newline-terminated
packet SHA256 is
`f790b1723be0f8ee61b7afdf5b7283182a2846cf99fb8c7fceb86d90c0b79e34`.

## 4. Verification and exact scope

Run:

```sh
python verify_exact.py
```

The fresh run passes 19 inherited Boolean-group checks, all 1,768 strict
packet truncations plus three malformed/trailing controls, all 44 one-step
rewrite orientations in a surrounding context, 1,000 natural-term-code
roundtrips, four universal Horn proofs with 16 inferences, and 256 finite
coordinate-update fixtures. The coordinate fixture is a separate small test
of the displayed update identity; it is not a finite model of FC13B or ZFC.

`output/alias.json`, `output/alias.bits` and `output/alias.equations` are the
recommended exact input. `reference/equational_search.py` can search this exact
JSON using its complete ideal enumerator. No unbounded search was run and no
consistency witness or refutation is claimed. Python's finite resources do not
supply termination or consistency information when such a search runs out of
resources.

The relative ordinary theorem is:

\[
 \mathrm{ZFC}\vdash
 \bigl(\neg\operatorname{Reach}_{1768}(N(d,d),d)
 \leftrightarrow
 \neg\operatorname{Reach}_{2324}(N(top,top),top)\bigr).
\]

Composing with the inherited FC13B calibration identifies both with Con(ZFC),
at that calibration's stated ordinary-proof scope. This contribution adds no
Lean/Rocq proof, no internal PA proof and no binary state count. A small binary
implementation still needs charged initialization, term/predicate codecs,
substitution, contextual replacement, a fair enumerator and proof that the
whole blank computation implements this target. The 1,768-bit size cannot be
divided by an assumed number of bits per state to assert a Busy Beaver bound.

## 5. Other formalisms considered

The current repository already contains extensive closure-schema, reflection,
finite class-theory, canonical-term, algebraic and quantified-NAND alternatives.
Source 70's exact packet and sources 40/42/44's equality-complete finite class
kernels offer concrete inputs for a replacement engine. Repeating a short
closure schema without charging its proof engine would not change the state
comparison. NBG's finite axiomatizability changes the source language and
requires its class apparatus; the recorded NBG translation does not already
supply a smaller complete packet and binary implementation.

A possible further fusion of the class-implication operation with the Boolean
algebra operation was investigated but is **not included in the theorem**.
FC13B shares its class-specialization function with a quantifier witness;
choosing unique extensional class representatives can destroy that shared
witness requirement. A correct model construction would need enough
representatives for each class and each required assignment. No saving from
this uncompleted construction is counted.

## Sources and attribution

1. ProveIt pinned source-70 intake and input/code artifacts:
   <https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md>.
2. McCune, Veroff, Fitelson, Harris, Feist and Wos, *Short Single Axioms for
   Boolean Algebra*, Journal of Automated Reasoning 29 (2002), Theorem 2;
   <https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf> and its companion
   proof files <https://www.cs.unm.edu/~mccune/papers/basax/>.
3. The exact inherited FC13B completion is credited through source 70 to
   `docs/incoming/zfc-sub245-research-20261018 (1).zip`, Git blob
   `c3ab3c8cb33ac535ec25ae6b8728217fedf4bd5b`. The delivered reference is frozen;
   no claim of authorship of that kernel or source-70 backend is made.

The general equational backend, fair ground-rewrite enumerator, packet format
and Boolean synthesis code are inherited unchanged. The contribution here is
the membership definition/elimination, constant-fusion model argument, and the
variable-capacity/alias trade, together with exact transformed artifacts and
small explicit proof certificates. The original consistency machine and
compiler remain credited to Mira-Cult, Jeff Ketchersid and Andrew James Wade,
with ProveIt's subsequent reductions and verification.
