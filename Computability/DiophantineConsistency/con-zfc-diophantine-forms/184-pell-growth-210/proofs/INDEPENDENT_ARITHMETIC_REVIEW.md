# Independent review of the 210-variable construction

Prepared 25 October 2026 for the ProveIt integration package. This review was
performed by a separately assigned AI research agent. It is not external human
peer review and is not an end-to-end Lean or Rocq verification.

## Conclusion

The new source changes and the emitted algebraic reduction passed this review.
The checked final equation is a sum of 150 squared quadratic residuals in 210
unrestricted integer variables. Its collected degree is exactly four, it has
5,282 nonzero monomials, its largest coefficient in absolute value is
1,099,511,627,776 = 2^40, and its largest residual coefficient is 1,048,576.

The final equation JSON has SHA-256

    20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a

The ordinary theorem composes the new arithmetic proof with the identified
inherited numerical-calculus/ZF/ZFC calibration. Finite coefficient checking
is not presented as proving those unbounded logical or Pell theorems.

## 1. The growth certificate is a substitute for a lower bound

The old exact request F=t^(2^20*t) is replaced by three literal quadratic rows,
with d=2^19:

    Z=tF,
    X^2-16Z^2-8ZF=1,
    F=d*t*(2u+1).

The center of the standalone Pell equation is 4t+1. Its classification does
not use the shared exponential-certification frame. Because F is nonzero,
there is a positive Pell index n with |F|=Y_n(4t+1).

For an odd center, v_2(Y_n)=v_2(n). Reduction modulo 4t gives
Y_n(4t+1)=n modulo 4t. Thus t divides n, and the displayed divisibility row
forces v_2(n/t)=19. Consequently n>=d*t. The recurrence lower bound gives

    |F| >= (8t+1)^(n-1) >= (8t)^(d*t-1).

The literal square-shell constructor estimate is

    constructor(u,v)+1 <= 8(M+1)^2     if 0<=u,v<=M.

Every local parameter is below t, and the retained constructor tree has maximum
depth 19. Therefore every relevant local label is strictly below

    L=8^(d-1)*t^d.

For t>=16, 8^(t-1)>=t, so |F|>=L^t. This is the precise estimate needed by
the label-product separation theorem. The new certificate does not in general
assert the parent's stronger, unnecessary inequality F>=t^(2^20*t).

The lower bound also exceeds t^t and the lcm bound needed by the generalized
binomial-CRT compiler. The remaining arithmetic front needs these proved lower
bounds and parity, not the old exact value of F.

## 2. Acyclic recovery of the growth ordinate's sign

Initially F can be signed. The new proof does not assume F>0 prematurely.
It has already proved that F is even, nonzero, and |F|>t. The even anchor C
also remains signed at this stage. Hence

    D=2(C+F+1)

is a nonzero even integer with |D|>=2. Its retained power certificate gives
x>=0 and q=D^x. With y=F(2v+1), the terminal beta endpoint excludes x=0.
The q-power at exponent y+1 then gives y>=|F|>0. If x=1, the initial endpoint
would give (y+1)u_0=-F, impossible because 0<|F|<y+1. Thus x>=2, and the
terminal endpoint strengthens this to x>=2+(t+1)y.

Now |q+1|>=2. The existing q+1 request at index F+t forces F+t>=0. Since
|F|>t, it follows that F>0. The same requests recover the nonnegative CRT
representatives. No new sign guard is needed.

## 3. The affine radix preserves both size and divisibility

The old base B[2+4(C+sum A_i)] is replaced by D=2(C+F+1). The exact retained
row B*eta=C+F+1 is essential: it proves D is a multiple of B and, after
x>=0 and N=B^x are recovered, N divides q=D^x.

The authenticated anchor cap gives every other nominal exponent absolute
value below |C|. Once signs are recovered, all binomial upper arguments,
including F+t, are at most C. Since D>2C, q>(2C)^x. Every coefficient used
in any of the retained binomial low parts is at most C^x<q/2^x. This is a
single uniform estimate for the initial binomial and the column range digits.
It supplies the strict remainder gap required by the common norm budget.

The initial digit gives B=binom(F+t,t) modulo q. Since B*eta=C+F+1 and eta
is a nonzero integer, |B|<=D/2<q/2. The true digit is below q/32. Therefore
B is exactly the positive binomial coefficient. This validates all later
uses of B>=2, N=B^x, and the binomial-CRT theorem.

## 4. Completeness and the odd binomial

The congruence and parity requirements can be met cofinally. Choose the
existing horizon t=16+4z^2 in a progression with t=16 modulo a sufficiently
large power of two, so v_2(t)=4. Set n_0=d*t. The odd-center valuation lemma
gives v_2(Y_(n_0))=23. Writing U=X_(n_0), V=Y_(n_0), Pell composition gives

    Y_(m*n_0)=V*Y_m(U).

The map m -> Y_m(U) permutes odd residue classes modulo each power of two.
This follows by bit lifting: incrementing m by 2^r changes Y_m(U) by exactly
2^r modulo 2^(r+1). Hence one can choose positive odd m so that
F=Y_(m*n_0)=2^23 modulo 2^K, with 2^K>t and the low t bits disjoint from
bit 23. The binary addition F+t is carry-free; the binomial coefficient is
odd. Also t divides F and F/(d*t) is odd, supplying the literal u witness.

After F and B, choose the beta spacing and x, then the other CRT
representatives, then the positive even cofinal anchor C, then D and q, and
finally the shared Pell frame. This order contains no circular choice.
The old anchor completion and the exact power witnesses then apply.

## 5. What the independent checker verifies

The accompanying verifier does not import the new producer or its polynomial
helpers. It reconstructs the actual 34-atom square frame; all 13 retained
principal Pell pairs, including the historical ordinate and AY offsets; the
entire orientation row as squared errors reduced by the individual norm rows;
and the anchor cap. It independently recognizes the removed old exact-power
block and checks the three new quadratic rows. Every source residual and every
collected quartic coefficient is compared exactly.

For the later algebraic stages, it uses the preserved independent projection
checker for all five common-Hessian eliminations and the affine consequence.
It independently implements all 79 elementary integer coordinate and residual
operations, verifies the forward coefficient identities, and reverses the
whole list to recover the original rows exactly. It expands the final sum of
squares independently and recomputes the reported metrics.

The check also deliberately corrupts growth, frame, orientation, cap,
coefficient, domain, projection, restoration, and invertibility data. All
mutations are rejected. The full run passes both ordinarily and under
python -O, so its requirements do not disappear when Python assertions are
removed.

## Remaining boundaries

The inherited arithmetic source-to-transcript theorem and C222/ZF/ZFC
calibration are mathematical dependencies. Their proof sources and provenance
must remain in the integration package. A fresh complete proof-assistant build
is not claimed. Global minimality, worldwide novelty, and the nonsolvability
of the final polynomial itself are not established. The construction proves
the conditional equivalence requested by the user, with a concrete reduction
against the inspected incoming quartic family.
