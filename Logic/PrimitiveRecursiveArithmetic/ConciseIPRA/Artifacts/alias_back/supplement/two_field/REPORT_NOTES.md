# Two-field streams for the conditional-copy calculus

## Result and boundary

The complete strict standalone checker `code/two_fields_compact.py` measures
609 significant Python tokens, 699 AST nodes, and 1644 normalized UTF-8 bytes
under CPython 3.12.14. The same stylistic simplifications applied to the
existing conditional-copy tree checker give the matched `code/tree_control.py`
at 629 / 732 / 1715. The new stream codec therefore saves 20 tokens, 33 AST
nodes, and 71 bytes against that control. The upstream file itself measures
646 / 748 / 1844.

This DOES NOT beat the inspected compact envelope 248 / 270 / 487. These
figures concern complete strict checkers for the full canonical Eq/D language;
the compact frontier uses a different public language and input contract.

The mathematical calculus is the existing conditional-copy calculus K from
the repository article, chapter 7, section "Conditional copy". No new
axiom deletion, mathematical principle, or literature-wide originality is
claimed. The result is a flat proof protocol with exactly two fields per
instruction and a smaller matched acceptance implementation. The inherited
tree format already has only two mathematical data choices in Use, one in
Close and none in Export; uniform field count is not itself an invariant
notion of mathematical simplicity.

## Syntax and theory

The numerical terms are zero, parameters, and the counter-aware
successor-seeded recursor R(n,a;i,u.h). Its equations are

    R(0,a;i,u.h) = S(a)
    R(S(n),a;i,u.h) = h[n/i,R(n,a;i,u.h)/u].

Successor is the abbreviation R(0,a;i,u.0). Full normalization is part of the
syntax, fully charged in the checker. In JSON, zero is 0, negative integers
are rigid free parameters, positive integers are positive de Bruijn indices,
and a recursor is [n,a,h]. The only formulas are equations [s,t] and paired
binders [B]. The paired binder binds two variables and reads

    D_{x,y} B := exists x (B(x,0) -> forall y B(x,y)).

A clause (A,B) reads A -> forall y B(y), or just forall y B(y) if A is the
empty antecedent []. The initial context consists of the reflexivity clause
([], [1,1]). With n clauses, the existing free numerical parameters are
1-n,...,-1; each scope-opening rule introduces b=-n and one clause.

The three existing inference families, all with normalized substitutions,
are Use, Close at the newest parameter (or 0 at the closed root), and Export
with its replacement inferred from the zero and first rows of its matrix.
Their precise definitions are implemented without modification from the
upstream conditional_copy checker. In particular the progressive Close mode
is selected exactly when its normalized zero instance is literally 0=0.
Export selects t only when the zero instance is 0=0 and the first instance
is literally b=t. In every other case it selects the fresh b itself.

## The two-field stack

The input is one JSON array. Its last item is the claimed closed formula.
The earlier items are two-element instruction lists, consumed from right to
left. There are exactly three instruction shapes:

1. `[j,t]`, with j an exact nonnegative integer: Use context clause j at
   the canonical term t. Its antecedent, if nonempty, is proved by the next
   instructions. The normalized instance must equal the current goal.
2. `[[],[]]`: Close the current goal [B]. There is no supplied matrix,
   witness, selector or branch goal. They are calculated from [B] and the
   context length. The following instructions prove the calculated
   successor instance under the calculated new assumption.
3. `[B,F]`, with B a nonempty formula: Export. The next instructions first
   prove [B] in the old context, then prove F under the opened clause.
   The inferred replacement is applied simultaneously once to F; the
   normalized result must equal the current goal, which was validated in
   the old numerical scope.

There are no unused placeholders or ignored subproof fields. Every active
term and formula is checked for exact integer/list syntax, sort, scope and
full canonical normality before being trusted. All recursor children are
checked, including children erased by normalization. The complete input
array must be consumed. Strings, dictionaries, Booleans, floats, unavailable
parameters, extra packet fields and unused prefixes cannot be accepted.

The smallest certificate is `[[0,0],[0,0]]`: Use reflexivity at zero to prove
0=0. A one-binder theorem D_{x,y}(0=0) has the certificate
`[[0,0],[[],[]],[[0,0]]]`.

## Equivalence proof

Fix a valid context g and an already validated canonical goal A. A stream
call is successful only if it consumes a finite initial segment of the
right-to-left instruction sequence and returns normally. The equivalent
tree judgment is `prove(p,g)=A` in the pinned upstream checker.

Proceed by induction on the successful stream execution tree, which is
finite because each recursive call consumes a new instruction. For Use,
the payload is the old clause index and term. If the antecedent is nonempty,
apply the induction hypothesis to its recursive proof; otherwise choose
null for the old ignored subproof field. The upstream tree is [j,t,p] and
has exactly the checked instance A.

For Close, the current goal uniquely supplies B. Both implementations set
the same n, b and newest parameter, perform the same normalized
substitutions, test the same literal zero instance, and extend by the same
assumption. The induction hypothesis for the branch produces the upstream
tree [B,p]. Its inferred formula is [B]=A.

For Export, the first recursive call supplies an upstream proof of [B].
Both implementations open exactly the same matrix at b and retain exactly
the same clause. The second induction hypothesis supplies an upstream proof
of F. Both compute the same zero and first rows, then apply the same one-pass
replacement to F. The explicit outer goal check identifies the result with
A. The upstream tree is [[],p,q]. Its final scope check is justified by the
initial check of A and equality of the results. This covers every successful
stream instruction, since every other packet shape rejects.

Conversely induct on a successful upstream tree derivation. Compute its
inferred formula A. Emit [j,t] for Use, [[],[]] for Close, and [B,F] for
Export, where B is the matrix inferred by its major proof and F is the
formula inferred by its branch. Emit each premise stream in the checker's
execution order. The same calculations establish success in each case.
Reverse the emitted instruction list and append A to obtain the input
stack. At the closed root this consumes the entire constructed input.

These are effective proof translations. The untrusted `convert.py` provides
both directions, and each reconstructed proof is submitted to the upstream
checker. Neither compiler is part of either trusted acceptance module.
The stream can be larger than the tree because Export now annotates its
matrix and branch formula; no general certificate-size improvement is claimed.

## Bi-interpretability

The previous proof establishes precisely the same closed consequences as
the existing calculus K, without changing any term, formula or ordinary
reading. Its established interpretations into and from full first-order
iPRA therefore apply unchanged. The numeral domains are whole, equality is
actual, and the numerical round-trip graphs remain x=y. This conclusion
depends on the written conditional-copy equivalence and arithmetic bridge
in the pinned repository article; this package has not produced a new Lean
or Rocq proof of them. Finite implementation checks do not prove the
bi-interpretation.

## Reproduction and provenance

Run `python3 verify.py` from this directory. The receipt records the exact
Python version, full-module sizes and finite checks. The positive fixture
suite is copied from the latest pinned conditional_copy artifact and
translated without manual proof edits. It includes naming at various scope
depths, arbitrary-witness compilation, genuinely used progress, successor
congruence, and inferred export underneath formula binders. Negative tests
cover false equations, Boolean/float aliases, wrong packet arities, scope
escapes, invalid erased recursor bodies, wrong clause indices and trailing
unconsumed data. Both normal Python and -O are exercised.

Source repository commit: 36d37fc1071fe289371f6bcd7dcfa0eac593a5a6.
Base path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
Inherited checker: Artifacts/conditional_copy/code/checker.py.
Inherited mathematics: docs/Article/chapters/ch07_wit.tex,
section "Conditional copy" and its cited arithmetic foundations.
The included reference checker and license retain the MIT-0 attribution.
