# Nearest-square compression of simultaneous strict positivity

## Result and boundary

The supplied `octic28.json` is an ordinary polynomial equation in **28 unrestricted integer variables**, a sum of squares of **14 residuals of degree at most four**, with exact total degree eight. It has an integer zero if and only if the pinned source's 30-integer octic has a zero. Consequently, composing with that source's mathematical correctness theorem, ZFC proves that this equation has no integer zeros if and only if Con(ZFC).

This is a strict reduction from 30 to 28 variables at the same degree, not the incorrect claimed 41-quartic-to-29-octic elimination. It changes the representation of *two simultaneous sign constraints*, not the arithmetic register elimination. The elementary lemma below is proved universally. No external novelty claim, global minimality claim, or new Lean/Rocq certificate is made. The inherited compiler and Pell proofs remain dependencies.

## 1. Elementary simultaneous-positivity lemma

For integers x,y define

    G(x,y,t) = xy - (t²-x-y+1)².

Then

    x>0 and y>0  iff  there exists an integer t with G(x,y,t)>0.

Soundness: G>0 implies xy>0. Thus x,y have the same nonzero sign. If both are negative, write x=-a,y=-b with a,b>=1. Then

    (t²-x-y+1)² = (t²+a+b+1)² >= (a+b+1)² > ab = xy,

contradicting G>0. Therefore both are positive.

Completeness: Let x,y>=1 and N=x+y-1. Then N>=1 and

    xy-N=(x-1)(y-1)>=0.

Put m=floor(sqrt(N)), and choose t=m when N-m²<=m, otherwise t=m+1. This is merely a witness-selection recipe in the proof, not an operation in the equation. In the first case 0<=N-t²<=m. In the second case, the integral inequalities m+1<=N-m²<=2m yield

    1 <= t²-N = 2m+1-(N-m²) <= m.

If N is a square, the chosen error is zero. Otherwise m²<N, and in either case

    (t²-N)² < N <= xy.

Hence G>0, as required. The argument uses only elementary integer arithmetic; it does not assume any consistency statement.

## 2. Turning the remaining inequality into a polynomial equation

For arbitrary integers p,q,r set

    Pos(p,q,r)=1+p²+q²+r(r+1).

This is always positive. Every positive integer n is representable: 4n-3 is positive and congruent to 1 or 5 modulo eight, so Legendre's three-square theorem applies. Exactly one square in such a representation is odd and the other two are even (by reduction modulo four). Writing them as (2r+1)²,(2p)²,(2q)² gives n=Pos(p,q,r).

Combining with Section 1,

    x>0 and y>0
      iff exists t,p,q,r in Z:
        xy-(t²-x-y+1)²-1-p²-q²-r(r+1)=0.          (PG)

Previously the two independent Pos representations used six private coordinates. Equation (PG) uses four, a reduction of two. If x and y have degree at most two in the retained coordinates, (PG) has degree at most four. Its square can therefore replace both old squared positivity residuals in an octic without increasing total degree.

This is an existential equivalence, not a bijection of witnesses and not a polynomial identity between old and new sums of squares.

## 3. Application to the exact 30-integer source

The source is the inert JSON file

    con-zfc-sign-and-norm/quartic42/companions/octic30.json

from the reviewed wave-nine source package. Its SHA-256 is

    91ee2d3d9a97d386fa2e8b939884d6cd846e866bb45b1efe945f11873e27b72c.

Its four fixed coefficient ports remain unchanged and denote the same authentic source34 tuple. They are fixed numerals, not variables. In particular q=beta J+1 and C=q-F-alpha are polynomial abbreviations. Put

    x=F alpha, y=F C.

Delete source residuals 13 and 14 (one-based), which say x=Pos(FA_pos1,FA_pos2,FA_pos3) and y=Pos(FC_pos1,FC_pos2,FC_pos3). Delete those six private coordinates. Insert (PG) with new private coordinates pair_root,pair_pos1,pair_pos2,pair_pos3. Keep every other source residual, including the separate eta*zeta positive guard, unchanged.

For any source zero, x,y>0. Section 1 selects pair_root and Section 2 represents the resulting positive G by Pos, supplying a new zero. Conversely, a new zero forces x,y>0; independently represent these two positive integers by Pos to restore the two deleted source rows and their six coordinates. All other coordinates and residuals remain unchanged. These two explicit existential maps prove the equivalence.

Counts: 30-6+4=28 integer variables and 15-2+1=14 residuals. The new guard is quartic since x,y are quadratic. Every unchanged source residual has degree at most four. The source exact-degree witness survives: the monomial a^4 f^4 has coefficient one in the sum of squares, and the new guard contains neither a nor f. Thus the total degree is exactly eight on the actual coefficient slice, not merely at symbolic generic coefficients.

## 4. Verification and limitation

`build_pair_guard.py` is newly authored code. It only reads the upstream JSON as inert data, parses its arithmetic with a restricted AST parser, and never executes upstream code. It verifies both deleted rows exactly, all retained rows, variable liveness, counts, total degree and coefficient [a^4 f^4]=1. It expands the final sum of squares into 551 monomials over the symbolic coefficient ring. It additionally tests 90,000 positive pairs and 152,561 signed triples as regression diagnostics; those finite checks do not replace the proof in Section 1.

The script uses a packaged byte-exact copy at `inherited/octic30.json`. The generated packets use portable coefficient-binding paths through `../integer_system_audit/BINDING.json` and its authentic source34 payloads; the inert inherited source remains byte exact. No coefficient recipe or native calibration is modified.

Section 5 records a recursive higher-degree companion. The primary same-degree improvement remains the precise 28-variable octic; no comparison to an unreviewed degree-sixteen frontier is asserted.

## 5. A nested 26-integer companion of degree sixteen

There is a further variable/degree tradeoff, not a same-degree improvement.
In the original octic30, write

    x=F alpha,
    y=F(beta J+1-F-alpha),
    z=eta(1-V+jc+hE-eta).

These are exactly the three quantities formerly required to be positive. The last expression is eta*zeta after the source's stated elimination map. It has degree three, while x,y have degree two.

Let g=G(x,y,t) and replace all three independent Pos rows by

    g z - (u²-g-z+1)² = Pos(p,q,r).

The pair lemma applied twice proves

    x,y,z>0 iff exists t,u,p,q,r satisfying this equation.

For soundness, the right side is positive; the outer pair lemma forces g,z>0, and the inner pair lemma forces x,y>0. For completeness first choose t making g>0, then choose u making G(g,z,u)>0, then choose a Pos representation. No bound or sign assumption is made on any new coordinate.

Delete all nine FA/FC/EZ private coordinates, and add only t,u,p,q,r. Thus the exact count is 30-9+5=26 integer variables. The twelve retained arithmetic residuals plus the new guard give thirteen residuals. The new guard has exact degree eight; its coefficient of t^8 is -1 and no retained residual involves t. Its square therefore has coefficient +1 at t^16. All retained squared residuals have degree at most eight, so the final polynomial has degree exactly sixteen.

`degree16_26.json` is the fully expanded residual packet. The auditor checks all three old guard identities, liveness, dimensions, the residual degree and the private-root exact-degree certificate. This is a 26-variable degree-sixteen companion, not a proposed improvement over the 28-variable octic under a fixed-degree objective. The same inherited source theorem proves the equivalence with finite ZFC refutability.
