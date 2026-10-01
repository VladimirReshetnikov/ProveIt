# A ten-operation ordinary-query bridge from a prescribed power

The [literal source](tseytin_affine_power_query_loader.py) loads Tseytin's
fixed-target query in **10=6M+4A operations and one comparison**, once a
containing source has paid for the exact relation

    Q=8^(32x), x>0.                                  (1)

One positive fixed program parameter records the primary program word.
The output `word` is its ordinary positive sentinel base-eight code.
The source uses only integer numerals, multiplication and subtraction;
no power, division or variable-length word operation is an arithmetic
primitive. Its standalone comparison polynomial has11 operations and
degree at most7, counting the program coordinate. The
[receipt](tseytin_affine_power_query_loader.json) records every numeral.

This is a conditional input bridge, not by itself a complete universal
equation. The power interface(1) and the complete word-history predicate
must both be composed and counted. It addresses the
[raw-loader obstruction](tseytin_group_completion_obstruction.md) by
exposing a paid power interface, rather than treating the exponential
query integer as a polynomial in ordinary x.

## 1. Adjusting the primary letter codes

Use the actual primary fixed-target reduction. A supplied finite group
presentation is converted to a special monoid by taking its relators
and both inverse-cancellation words for each generator. Put K0 empty,
add distinct symbols alpha,beta, and define

    phi(z1...zk)=a b^n(z1) a b^n(z2) ... a b^n(zk) a,
    S=twin(phi(alpha K0 alpha K1 alpha ... Km alpha)),
    twin(a)=c, twin(b)=d.

The primary theorem allows arbitrary distinct nonnegative code numbers
with n(alpha)=1 and n(beta)=0. For the two distinguished source generators
choose

    n(a_source)=2,     n(a_source^-1)=3,
    n(b_source)=31,    n(b_source^-1)=63.              (2)

Assign all remaining signed generators distinct numbers starting at64.
Here the source group letters are distinct from the five output semigroup
letters. The checker implements the full program recipe, including K0
and both ends of every separator, and decodes it back independently.

For ordinary positive x use the same freely reduced commutator as the
reviewed primary reduction:

    a_x=b_source^(-x) a_source b_source^x,
    r_x=a_x a_source a_x^(-1) a_source^(-1).

The full output word is u_x=S phi(beta r_x beta). The primary theorem
gives u_x=aaa in C2 exactly when r_x=1 in that supplied group. Changing
the injective code numbers to(2) does not change this equivalence.

The tail phi(beta r_x beta) is exactly the following concatenation of
output-letter blocks:

    a,
    (a b^63)^x, abb, (a b^31)^x, abb,
    (a b^63)^x, abbb, (a b^31)^x, abbb, aa.           (3)

It has length192x+17. In particular, its variable block scales are Q^2
and Q under(1), and its total scale is8^17 Q^6. This is why one prescribed
power suffices for every variable piece of the query.

## 2. An integer polynomial after clearing one fixed denominator

Encode output letters a,b,c,d,e as base-eight digits1,2,3,4,5. Write raw(v)
for the usual positional value and enc(v)=8^|v|+raw(v), so enc(empty)=1.
Then

    enc(Sv)=enc(S)*8^|v|+raw(v).                       (4)

Set B=8^32 and Delta=B^2-1. For a block of length L, equal to a b^(L-1),
its x repetitions have positional value

    raw(a b^(L-1)) * ((8^L)^x-1)/(8^L-1).            (5)

Only L=32 and64 occur in(3). Under(1) their numerators are Q-1 and Q^2-1,
and both denominators divide Delta. Concatenation multiplies these values
only by fixed powers of8 and powers of Q; it never multiplies two raw
block values. Therefore clearing the single fixed denominator Delta
makes every coefficient integral.

Exact polynomial concatenation of(3) gives coefficients h_i satisfying

    Delta*raw(phi(beta r_x beta))=sum_(i=0)^6 h_i Q^i,
    h_2=h_5=0, h_6>0, h_0,h_1,h_3,h_4<0.            (6)

The source generates these coefficients with rational arithmetic only
at compilation time and asserts exact integrality. The receipt lists
their full integer values. The construction is a finite explicit recipe
for fixed numerals, not a runtime arithmetic instruction or division.

An independent suffix-contribution calculation gives the shorter exact
forms below, with B=8^32:

    h6=8^15*(65B^2-72)/7,
    h4=-8^12*(B^2+B-512),
    h3=-8^9*(B^2-512B-512),
    h1=-8^5*(B^2+B-4096),
    h0=(-65B^2+229376B+229441)/7.

The displayed divisions are exact fixed-numeral recipes: B=1 modulo7.
They also directly give the signs in(6).

Let c_i=-h_i for i in{0,1,3,4}, and choose the single positive program
coefficient

    A=Delta*8^17*enc(S)+h_6.                          (7)

Equations(4)--(7) prove the exact query-code relation

    Delta*word=A Q^6-c_4 Q^4-c_3 Q^3-c_1 Q-c_0.       (8)

For a valid program recipe and(1), the right side is Delta times the
positive integer enc(u_x). Since Delta>0, the comparison in(8) uniquely
forces that value of `word`. Conversely that value is a positive solution.
No separate length, remainder or digit-typing witness is hidden here.
Invalid fixed values of A have no claimed universal-program meaning.

## 3. Literal arithmetic and compositional interface

The counted graph evaluates(8) by the sparse Horner formula

    Q2=Q*Q,
    N=(((A*Q2-c_4)*Q-c_3)*Q2-c_1)*Q-c_0,
    T=Delta*word,
    compare N=T.                                    (9)

The numerator uses five multiplications and four subtractions; the
denominator multiple adds one multiplication. Every numeral product is
charged. Equality is a certificate comparison, not an arithmetic gate.
Subtracting T from N gives the standalone11-operation polynomial.
All10 graph rows reach that output. Its highest-degree term is A Q^6,
so the stated total-degree bound is7, or6 after fixing the program.

The public inputs of this module are positive A,Q,word. A complete
composition should keep A as the fixed program parameter, derive Q from
ordinary positive x using a proved and counted power gadget, and treat
word as a positive witness consumed by the complete C2 history source.
The comparison in(9) must remain in the aggregate finalizer. Arithmetic
identities between this graph and its rational compilation recipe do not
make the power interface or the history relation free.

## 4. Checks and remaining boundary

The source builds216 literal primary query words across three ranks,
three presentations and24 ordinary inputs. Each is decoded, its exact
length is checked, and its sentinel code satisfies the literal10-gate
source. Another432 one-unit output perturbations have the exact nonzero
residual plus or minus Delta. A further128 arbitrary signed assignments
compare the complete Horner polynomial to(8), independently of(1) and
the valid-program recipe. The source checks integrality and the two zero
coefficients in(6), the literal ledger and the degree bound.

Run `python3 tseytin_affine_power_query_loader.py`; `--write` regenerates
the receipt. Author generation and fresh replay pass. Independent full
proof/source/primary-code-permission review and a further fresh replay
pass without findings. The separate suffix calculation verifies all seven
coefficients;24 additional presentations,144 independently spelled queries,
576 perturbed outputs and384 full formal outputs (192 signed) pass.
All11 polynomial gates are live and the degree bound is7. No operation bound for a complete ordinary-input universal
equation is asserted until the power and word-history sources are joined.
