# A seven-equation algebraic target for consistency search

Research note, 16 October 2026. This note proves an algebraic compression and
provides an executable generic proof-search kernel. It does **not** provide an
expanded ZFC-specific target term, a binary Turing-machine table, or a new state
record. The construction uses published reduction theorems at the mathematical
theorem level; their full compiler is an outstanding implementation task. The
compression below is derived here, with no claim that it has not appeared before.

## 1. The proposed division of work

Encode all foundational strength in one fixed ground equality query. Search for
its derivation from seven fixed universally quantified equations. A candidate
certificate specifies a finite sequence of local replacements, including the
equation, direction, ground substitution, and one-hole context at every step.
The checker needs term constructors and structural equality. It does not need
first-order variable binding, a free-variable side condition, unification, or an
axiom-schema recognizer.

The semantic bridge uses diagonal-free cylindric algebras of dimension three,
written Df3. Andréka and Németi published a computable, validity-reflecting
translation of full first-order logic into the associated one-generator logic.
Their Theorem 1.6(i) and Remark 1.3(ii) give the exact theorem needed here:

> A first-order sentence can be translated effectively into an identity
> `t(p) = 1` in one generator, such that the identity holds in all Df3 algebras
> exactly when the original sentence is logically valid.

This paraphrases the combination of two statements, rather than quoting a
separate theorem under that wording. The published chapter is *Reducing
First-order Logic to Df3, Free Algebras* (2013), pp. 15–35,
DOI [10.1007/978-3-642-35025-2_2](https://doi.org/10.1007/978-3-642-35025-2_2).
An [author manuscript](https://old.renyi.hu/pub/algebraic-logic/CAIII-ANpaper.pdf)
contains both numbered results. Its proof references the authors'
earlier paper and supplementary Part II notes. The present artifact has not
implemented or independently machine-checked that translation.

The main additional observation is that, for **identities**, the three closure
operators of Df3 can be represented using one closure and a Boolean automorphism
whose cube is the identity, with only one explicit commutation equation. This must not be
silently extended to arbitrary equational premises; Section 5 gives a
counterexample. Placing the set-theoretic payload in the query avoids that error.

## 2. An explicit basis of seven equations

Use binary NAND `x | y` and two unary operations `q` and `r`. Define abbreviations

\[
 \neg x=x\mid x,\qquad
 x\vee y=(x\mid x)\mid(y\mid y),\qquad
 1(x)=x\mid(x\mid x).
\]

Every equation below is universally closed. There are no hidden side conditions.

| Name | Equation | Symbol occurrences, including equality |
|---|---|---:|
| Sh1 | `(x | ((y | x) | x)) | (y | (z | x)) = y` | 15 |
| Rhom | `r(x | y) = r(x) | r(y)` | 10 |
| R3 | `r(r(r(x))) = x` | 6 |
| Qext | `(x | x) | (q(x) | q(x)) = q(x)` | 12 |
| Qadd | `q((x | x) | (y | y)) = (q(x) | q(x)) | (q(y) | q(y))` | 20 |
| Qcomp | `q(q(x) | q(x)) = q(x) | q(x)` | 12 |
| Qrot | `q(r(q(r(r(x))))) = r(q(r(r(q(x)))))` | 13 |
| **Total** | **Seven equations, three operation symbols** | **88** |

This count includes each operation occurrence, each variable occurrence, and
each equality sign; it excludes punctuation and universal quantifiers. It is a
description statistic, **not** a binary encoding length or a TM state count. In
particular it excludes the set-theoretic target term.

Sh1 is the known shortest 15-symbol single axiom for Boolean algebra in the
NAND signature. Its proof and minimality result are due to McCune, Veroff,
Fitelson, Harris, Feist, and Wos, *Short Single Axioms for Boolean Algebra*,
Journal of Automated Reasoning 29 (2002), 1–16,
DOI [10.1023/A:1020542009983](https://doi.org/10.1023/A:1020542009983).
See equation (1.5) in the
[author PDF](https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf).
The claimed minimality is specifically for a single Boolean axiom under their
length convention, not for this extended theory.

Let `Ecyc` denote this seven-equation theory. The one-element algebra is allowed,
as usual for a variety. The final disequation excludes it when necessary.

### Lemma 1: the missing closure identities are derivable

In any `Ecyc` algebra, the NAND reduct is a Boolean algebra by Sh1. Qext is
`x ∨ qx = qx`, so `q` is extensive. Qadd states finite additivity, hence
monotonicity. Qcomp is

\[
 q(\neg qx)=\neg qx.
\]

Substitute `¬qx` for `x` in Qcomp. This gives

\[
 q(\neg q(\neg qx))=\neg q(\neg qx).
\]

Replacing the inner `q(¬qx)` by `¬qx` on both sides and using Boolean double
negation yields `q(qx)=qx`. Thus no separate idempotence equation is needed.
Extensivity at `1` gives `q1=1`; Qcomp at `1` then gives `q0=0`. Consequently `q`
is a complemented closure operator in the Df3 sense.

Rhom says that `r` preserves NAND, hence all Boolean operations. R3 makes `r`
bijective, with inverse `r²`. It is therefore a Boolean automorphism.

### Lemma 2: every cyclic algebra has a Df3 reduct

Define, with exponents interpreted modulo three,

\[
 f_i=r^i q r^{-i},\quad i=0,1,2.
\]

In explicit term syntax these are

\[
 f_0x=qx,\qquad f_1x=r(q(r(r(x)))),\qquad
 f_2x=r(r(q(r(x)))).
\]

Conjugating a complemented closure by a Boolean automorphism gives another
complemented closure. Qrot says precisely `f0 f1 = f1 f0`. Conjugating this
identity by `r` gives `f1 f2 = f2 f1`; conjugating by `r²` gives
`f2 f0 = f0 f2`. Hence the three derived operators commute pairwise.
The reduct therefore satisfies the standard finite equational definition of
Df3: a Boolean algebra with three commuting complemented closures. The
definition is given explicitly in Section 2 of Andréka–Németi's
[2011 manuscript](https://arxiv.org/pdf/1111.0995).

## 3. A product construction proves identity reflection

Let `A` be an arbitrary Df3 algebra, with Boolean NAND and closures `f0,f1,f2`.
Form the Cartesian cube `B=A³`, with NAND coordinatewise, and define

\[
 r(a_0,a_1,a_2)=(a_1,a_2,a_0),\qquad
 q(a_0,a_1,a_2)=(f_0a_0,f_1a_1,f_2a_2).
\]

The Boolean equation holds coordinatewise. Rotation preserves NAND and has
order dividing three. Extensivity, additivity, and complemented closure of `q`
hold coordinatewise. For every `i,j` modulo three,

\[
 \bigl(r^iqr^{-i}(a)\bigr)_j=f_{i+j}(a_j).
\]

The original closures commute, so Qrot holds at each coordinate. Thus `B` is an
`Ecyc` algebra.

Let `τ` replace every Df3 operator `fi` by the displayed conjugate term, leaving
NAND unchanged. For any Df3 term `t`, any valuation `v` in `A`, and the diagonal
valuation `vΔ(x)=(v(x),v(x),v(x))` in `B`, the first coordinate of
`τ(t)` evaluated in `B` is exactly the value of `t` in `A`. The other two
coordinates are the values of the two cyclic relabelings of `t`. This follows
by induction on the term. More generally the first projection of the derived
Df3 reduct of `B` onto `A` is a surjective Df3 homomorphism.

### Theorem 3: identity validity is preserved and reflected

For all Df3 terms `s,t`, with any finite number of variables,

\[
 \mathrm{Df3}\models s=t
 \quad\Longleftrightarrow\quad
 E_{\rm cyc}\models\tau(s)=\tau(t).
\]

For left-to-right, every `Ecyc` algebra has the Df3 reduct of Lemma 2. For
right-to-left, a counterexample `A,v` to `s=t` lifts to the cube just constructed;
the first coordinate still differs. This is an explicit countermodel lift,
not an assertion that `A` itself can be expanded with a suitable symmetry whose
cube is the identity.

By equational completeness this is also an equivalence of equational
derivability. There are syntactic proof translations if desired. In the forward
direction replace operators by conjugate terms and insert fixed derivations of
the Df3 basis. In the reverse direction represent every cyclic term by three
Df3 terms: NAND acts coordinatewise, `r` rotates the triple, and `q` applies
`f0,f1,f2` to the three coordinates. Each cyclic axiom becomes three derivable
Df3 identities. Applying the transformation to an equational derivation and
taking the first coordinate recovers the original identity. Variables can be
sent to diagonal triples for the final query, or initially to triples of fresh
variables and then diagonally specialized.

## 4. Obtaining one consistency query

Choose a finite first-order theory conservative over ZF. A concrete source is
Andréka and Németi's finitely axiomatized cylindric Gödel–Bernays theory, CGB.
Their [2013 nine-page paper](https://old.renyi.hu/pub/algebraic-logic/ANCGB13.pdf)
is in Hungarian. Theorem 1 (printed page 189) states

\[
 \mathrm{ZF}\vdash\varphi
 \quad\Longleftrightarrow\quad
 \mathrm{CGB}\vdash\varphi^V
\]

for every set-theoretic sentence `φ`. Its proof explicitly describes syntactic
proof transformations. The finite source axioms provide class Boolean and
cylindric operations, class products, images of sets under class functions, the
usual elementary set-existence axioms, and Foundation. All notational
abbreviations must be expanded before a compiler is considered complete.
Alternatively a standard finite GB presentation with the same proved
conservativity can be used.

Let `σ` be the conjunction of the finite CGB axioms, as a sentence of ordinary
first-order logic with equality and no function symbols. Then

\[
 \operatorname{Con}(\sigma)
 \leftrightarrow\operatorname{Con}(\mathrm{ZF})
 \leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The second equivalence uses the usual relative consistency of Choice via the
constructible universe; inclusion of ZF in ZFC gives the other direction. It is
also possible to add the set-relativized axiom of Choice to finite CGB directly.
No assumption of actual consistency is needed to prove these relative
consistency equivalences. For primary historical sources see Gödel's
[1938 announcement](https://doi.org/10.1073/pnas.24.12.556) and
[1939 proof sketch](https://doi.org/10.1073/pnas.25.4.220); the latter explicitly
treats Zermelo's theory with and without the substitution axiom.

Apply the published first-order-to-Df3 validity translation to **the sentence
`¬σ` itself**. Let the resulting identity be `tσ(p)=1`. Then

\[
 \sigma\text{ is inconsistent}
 \quad\Longleftrightarrow\quad
 \models\neg\sigma
 \quad\Longleftrightarrow\quad
 \mathrm{Df3}\models t_\sigma(p)=1.
\]

The first equivalence is first-order completeness for a finite theory. The
published translation is not generally a Boolean homomorphism: Remark 1.8(iv)
specifically warns that it need not preserve negation. Replacing `tr(¬σ)` by
`¬tr(σ)` would therefore be unjustified. Translating the whole negated sentence
also avoids using any invalid preservation-of-premises claim.

Introduce a fresh constant `c` and put

\[
 s_\sigma=\tau(t_\sigma)(c),\qquad
 u=c\mid(c\mid c),\qquad
 T_\sigma=E_{\rm cyc}\cup\{s_\sigma\ne u\}.
\]

This is seven universal equations and one ground disequation in one binary
operation, two unary operations, and one constant. A many-symbol target term
may contain considerable information despite the small number of axioms.

### Lemma 4: the fresh constant introduces no hidden premise

Since `c` does not occur in `Ecyc`, an identity `a(p)=b(p)` holds in all cyclic
algebras if and only if the ground equation `a(c)=b(c)` holds in all expansions
by `c`. One implication is substitution. For the other, expand any algebra by
an arbitrary choice of the interpretation of `c`. Equivalently, a finite
equational derivation with fresh `c` can be uniformly renamed to a fresh
variable. If the identity fails at `p=d`, interpreting `c` by `d` witnesses
failure of the ground equation.

This point is why a **disequation** is the appropriate final payload. In the cube
construction a differing first coordinate suffices to make the two ground
terms unequal; their other coordinates need not satisfy any additional
equations. There is no claim that the diagonal element makes three cyclic
copies of an arbitrary premise true.

### Corollary 5: the finite theory has the required consistency strength

\[
 \operatorname{Con}(T_\sigma)
 \quad\Longleftrightarrow\quad
 \operatorname{Con}(\mathrm{ZFC}).
\]

Indeed, `Tσ` is inconsistent exactly when `Ecyc` proves `sσ=u`. If the equation
is not derivable, the ground term algebra modulo the congruence generated by
`Ecyc` is a model of the equations in which the two specified classes differ.
This gives a direct model of the disequation; it is not necessary to invoke
first-order completeness a second time. Lemma 4, Theorem 3, and the published
validity translation complete the chain.

These are ordinary mathematical relative-consistency arguments formalizable
in ZFC. The artifact does not contain a ZFC proof object, a checked
implementation of the published validity translator, or the actual expanded
term `tσ`. The construction identifies exactly what such an implementation
must establish. The 2013 published theorem is preferable to citing only the
2011 preprint's Theorem 2.2: that earlier manuscript qualifies the scope of its
included proof and develops a pairing-guarded fragment in detail. The present
proposal relies on the later general published statement, not on an inferred
claim of unrestricted completeness for naive three-variable semantics.

## 5. A necessary limitation: arbitrary premises are not preserved

It would be incorrect to strengthen Theorem 3 to

\[
 \mathrm{Df3}+\Gamma\models s=t
 \quad\Longleftrightarrow\quad
 E_{\rm cyc}+\tau(\Gamma)\models\tau(s)=\tau(t)
\]

for arbitrary universal-equation premises `Γ`.

For a counterexample take `A=P({0,1})`. Let `f0` and `f2` be the identity, and
let `f1` be the indiscrete saturation: `f1(∅)=∅` and `f1(X)={0,1}` for every
nonempty `X`. These are pairwise commuting complemented closures. Thus `A`
satisfies `Γ={∀x f0(x)=x}` but fails `∀x f1(x)=x` at `{0}`.

After translation, however, `Γ` becomes `∀x q(x)=x`. Every cyclic algebra
satisfying that equation also satisfies `r q r²=r r²=id`. Hence
`Ecyc+τΓ` proves the translated conclusion. This disproves arbitrary-premise
conservativity. Requiring all cyclic conjugates of `Γ` would strengthen the
original premise and does not repair the stated equivalence.

In the product `A³` the particular diagonal tuple associated with `{0}` is
sent by `q` to a tuple whose middle coordinate changes. This is the concrete
reason that merely placing a source presentation on a diagonal generator does
not ensure the translated premises. The validity-query construction of
Section 4 does not make this step.

## 6. A fully ground proof-search kernel

### Lemma 6: ground rewrite chains are complete

For a finite universal equational basis `E` and ground terms `s,t`,

\[
 E\vdash s=t
\]

if and only if there is a finite sequence `s=u0,u1,...,un=t` in which each
adjacent pair is obtained by replacing a ground instance of one side of an
equation of `E` by the corresponding instance of its other side, in a one-hole
ground context, in either direction.

For soundness, every such step is an application of substitution and
congruence, and the whole chain uses transitivity. For completeness, define
`s~t` by existence of such a chain. It is an equivalence relation and a
congruence, and contains every ground instance of every axiom. The quotient of
the ground term algebra by `~` satisfies every universal axiom: a tuple of
elements has ground representatives, to which that axiom can be instantiated.
If no chain exists, the quotient separates `s` and `t`; soundness of equational
logic implies the equation cannot be derivable. Equivalently, any auxiliary
variables in a finite equational proof can be replaced by the available
constant, yielding the needed ground instances.

### The implemented enumeration

`cyclic_algebra.py` implements the seven exact equations, a Df3-to-cyclic term
translation, and a generic ground certificate checker. It uses the Cantor
pairing function

\[
 \langle a,b\rangle=(a+b)(a+b+1)/2+b.
\]

Every natural number is a term code. Code 0 is `c`; for a positive code `k`,
write `k-1=3a+j`. Tags `j=0,1` mean `q(term(a))` and `r(term(a))`; tag 2 uses
`unpair(a)=(b,d)` and means `n(term(b),term(d))`. Every child code is smaller
than its parent. The inverse encoder is explicit.

Every natural number is also a one-hole context code. Code 0 is the hole;
write `k-1=4a+j` for positive `k`. The four cases are a context under `q`, under
`r`, in the left argument of NAND with a coded ground right sibling, and in
the right argument with a coded ground left sibling. Cantor pairing separates
the binary-case subcodes. The recursive subcontext code decreases strictly.

A move records an axiom index in `0,...,6`, one direction bit, a context code,
and three ground substitution codes for `x,y,z`. A fixed pairing/tag encoding
enumerates every such move. The finite-list encoding is 0 for the empty list
and `1+pair(head,tail)` for a nonempty list; its tail is strictly smaller.
Thus every natural number describes a finite, syntactically well-formed
candidate chain. The checker reconstructs each pair of endpoints, compares
the left endpoint with the current term, and continues from the right.

Enumerating natural candidate codes in increasing order therefore halts
exactly when the equality query is derivable. Each particular candidate takes
finite time. The actual proof search can be extraordinarily slow; speed is
not the principal objective of a Busy Beaver state-count construction.

Core term validation, term encoding/decoding, context application, list decoding,
and structural equality use explicit iterative stacks rather than the Python
recursion limit. Pattern substitution is recursive only through the fixed,
bounded-depth seven axiom patterns; it does not traverse substituted terms.
The display/counting helper, finite-model evaluator, and optional Df3 translator
are research utilities and retain ordinary recursive implementations. The
core search is not dependent on those utilities. The JSON command-line wrapper
has the usual host parser/resource limits; no physical Python process has
unbounded resources. The natural-number search algorithm itself has no
artificial depth cutoff or incomplete search bound.

Given the **as-yet unimplemented** fixed target `sσ,u`, the resulting search
program would satisfy

\[
 \text{program does not halt}
 \leftrightarrow E_{\rm cyc}\nvdash s_\sigma=u
 \leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Compiling that program, including initialization of its target, into a standard
blank-tape binary TM and proving the simulation is a separate required step.

## 7. Verification included in the artifact

Run `python3 test_cyclic_algebra.py` with the standard library. The captured
result is `verification.json`; `basis.json` gives the exact syntax tree of
every axiom, and `demo.json` gives a small accepted and rejected example.

The tests perform:

* 270,592 exhaustive identity evaluations on a 64-element product algebra,
  including all assignments needed by every one of the seven equations. Its
  `q` and `r` do not commute, guarding against the accidental stronger axiom
  `qr=rq`.
* 1,200 deterministic seeded translation tests using three distinct commuting
  cylinder closures on the 256-element Boolean algebra of subsets of an
  eight-point cube. Every product coordinate is checked against the matching
  cyclic relabeling, rather than checking only equal closures.
* The explicit arbitrary-premise counterexample from Section 5.
* A nontrivial two-step rewrite certificate, ten deliberately malformed or
  incorrect certificates, seven malformed terms, and 5,000 round trips each
  for the term, move, and finite-list codecs.
* Ground terms and contexts nested 2,000 unary operations deep, including
  encoded certificate validation and rejection of a changed target, without
  changing the Python recursion limit. A cyclic Python container is rejected.

The finite-model and randomized checks are sanity checks, not proofs of the
general theorems. The mathematical proofs above supply the general arguments.
None of these tests validates an actual ZFC-specific term or a small TM.

## 8. What would make this a competitive machine proposal

The favorable feature is a fixed local proof checker: its input language has
one binary node, two unary nodes, and one ground leaf; each rewrite is backed
by a constant finite basis. This removes binding and schema machinery from
the run-time verifier. The finite source theory and all translation complexity
move into one target term.

That move can lose. A pairing-based full-first-order translation followed by
the cyclic translation may produce a large term. Expanding `f1` and `f2`
replaces each occurrence with four unary nodes. NAND expansions duplicate
subterms. The 88-symbol axiom total does not bound this payload. A shared
straight-line representation may help the loader but needs a proved expansion
or evaluation protocol. A tuple or bitstream parser can also cost more states
than the current specialized register-machine frontend.

The decisive next experiment is therefore to implement the finite source and
the published translation with exact source-to-query proof obligations; emit
the literal target term and a size manifest; compile both the checker and its
blank-tape initializer; and compare the complete transition table against the
current 253-state candidate. The cyclic basis can be benchmarked alongside a
direct Df3 basis to find out whether fewer primitive operations outweigh the
longer conjugate terms. If the complete machine is not smaller, the construction
still provides an independently structured equivalence target and a compact
proof-search reference.
