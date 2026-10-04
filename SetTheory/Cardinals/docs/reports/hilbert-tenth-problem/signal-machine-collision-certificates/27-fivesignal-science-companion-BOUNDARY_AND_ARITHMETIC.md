# Exact boundary geometry and rational-input arithmetic

Research companion, 4 October 2026. This does not replace the collision-gadget proof. The physical claim is conditional on auditing the five-signal macro and its exact 36-row chamber in the construction packet. All calculations below were independently derived from the endpoint formulas. No physical simulator or stored collision schedule was executed.

## 1. Coordinates and exact return

The outgoing section has a stationary left wall at 0, a +1 shuttle there, stationary data markers at 0<x<y<D, and a stationary right wall at D. Its three positive gap coordinates are (x,y−x,D−y). Put X=x−D/3, Y=y−2D/3.

The proposed macro first performs the centered shears Sx(−1/2), Sy(4/5), Sx(−1/2), then scales x,y,D by 1/2 in that order. Its return in (D,X,Y) is

    (D,X,Y) -> (D/2, 3X/10−2Y/5, 2X/5+3Y/10).

Thus normalized (u,v)=(X/D,Y/D) rotates by

    R = [[3/5,−4/5],[4/5,3/5]].

The gap return is M=(1/30)[[7,−2,10],[14,11,−10],[−6,6,15]]. The coordinate conjugacy and all displayed endpoint identities are checked by `independent_algebra.py`, an owned exact rational-algebra script using only Python's standard library. This is not a trajectory simulator.

## 2. Strict polygon and exact inradius

The companion GUARDS.txt contains 36 linear strict rows aD+bX+cY>0. Each a is positive. On D=1 the exact legal one-macro domain is therefore an open convex rational polygon P containing (0,0). It is bounded because the starting order 0<x<y<1 is among its guards.

The unique row with least squared distance a²/(b²+c²) from (0,0) is

    D/15 − 3X/5 + 13Y/10 > 0.

Its squared distance and contact point are

    r² = 4/1845,
    p = (4/205, −26/615).

All other rows have strictly larger supporting-line distance. The exact comparison of these 36 rational squared distances is checked independently. The claim is about the supplied essential endpoint rows; physical completeness still depends on the companion gadget chronology proof.

R has infinite order. Its eigenvalue z=(3+4i)/5 is not a root of unity: if it were, z+z^(−1)=6/5 would be an algebraic integer, whereas a rational algebraic integer is an integer. Consequently the orbit of every nonzero planar point under R is dense on its circle.

It follows that

    K := intersection_(n>=0) R^(−n)P
       = {w: ||w||²<4/1845}
         union ({w: ||w||²=4/1845} \ {R^(−n)p:n>=0}).

Proof: an interior-radius circle satisfies every row uniformly strictly. A larger-radius circle has a nonempty arc where the nearest row is negative; density forces a future failure. On the critical circle, all other rows are uniformly strict, and the nearest row vanishes exactly at p. Therefore all finite macro prefixes are valid precisely for w in K.

The full real initial-gap set is the positive homogeneous cone over K, by D>0. This set is not semialgebraic. Otherwise its D=1 section and intersection with the algebraic critical circle would be semialgebraic. The excluded subset of that circle would then also be semialgebraic, but it is countably infinite. A semialgebraic subset of a circle is a finite union of points and arcs; a countably infinite such set is impossible.

This failure is not just a failure of degree-two signs. It rules out any finite real polynomial-sign description, and any finite existential-real polynomial description, of the full real validity set. It says nothing by itself against existential-natural Diophantine descriptions of rational encodings.

## 3. Which collision causes the missing point?

At the contact p, the initial positions are

    D=1, x=217/615, y=128/205.

After the first full x-shear, x becomes 46/123. The first reflected translation in the y-shear uses the expansion factor 5/3 on the right-wall distance D−y. Here

    D−y = 77/205 = (3/5)(D−x),

so its expansion endpoint coincides exactly with the stationary x marker. The shuttle, the moving y marker, and the stationary x marker meet together. The proposed word specifies only its binary shuttle/y collision, so completeness rejects that prefix. The incoming velocities are distinct (−1,−1/4,0). For R^(−n)p, the same forbidden triple contact occurs in macro n. This identifies an actual omitted collision, rather than an abstract sign boundary.

## 4. Rational-input membership is elementary and decidable

Let D,x,y be rational and D>0. Compute w=(u,v)=((x−D/3)/D,(y−2D/3)/D) exactly. Compare u²+v² with r²=4/1845. Below r², accept; above, reject. On equality, put

    eta=(u+iv)/(p_x+i p_y) in Q(i).

The input is invalid exactly when eta=((3−4i)/5)^n for some integer n>=0.

There is a finite elementary test with no orbit search. Write eta=A+iB in reduced rational form, and let q be the least common positive denominator of A and B. The common denominator of ((3−4i)/5)^n is exactly 5^n. For n>=1, the numerator pair of (3−4i)^n reduces to (3,1) modulo 5, because (3+i)^2=(3+i) in F_5[i]. Thus neither component has a factor of 5, and no cancellation of the denominator is possible.

1. If q is not a power of 5, eta is not a forbidden power: accept.
2. If q=5^n, that n is forced. Compare eta exactly with ((3−4i)/5)^n using integer powering. Reject iff equal; otherwise accept.

The orientation n>=0 matters. For example eta=(3+4i)/5 is a forward rotation of p, and is valid on the boundary; it is not a nonnegative inverse power. Density is never used as a decision procedure.

After an explicit signed-integer/positive-denominator encoding, the rational validity predicate is recursive, hence Diophantine by MRDP. No unique-witness, fixed-degree, or economical Diophantine compiler is asserted by this observation. In particular the nonsemialgebraic real-input theorem does not contradict Report56's arithmetic framework.

## 5. Zeno clock

Every legal macro halves D. During it every marker and shuttle stays in [0,D] at that macro's start, and the fixed finite primitive list has duration bounded by a fixed multiple of D. Hence every valid input is Zeno; all five ordered positions converge to the fixed left wall 0. A simple proof bound is 83D per macro, so total time is at most 166D initially.

Direct duration algebra gives the one-macro time

    ell(D,X,Y) = (37264/855)D + (36497/1425)X − (10227/475)Y.

The two full shuttle transfers contribute 2D. A left-based L_Z(u) primitive lasts 2(Z+uZ); a return-to-base H_Y(v) primitive lasts 2Y. Reflected versions use distances from D. The three final half-scaling primitives together contribute 3(x_rot+y_rot+D).

Summing the geometrically contracting return gives

    T(D,X,Y) = (74528/855)D + (53102/3705)X − (144302/3705)Y.

The exact row identity T−T∘M=ell is checked by independent rational Gaussian elimination. It is conditional on actual macro legality, not a replacement for the guard test. For rational data the accumulation time is rational, consistent with Report56's arbitrary-population rational-limit theorem.

## 6. Prior work and scope

Dai and Xia, *Non-Termination Sets of Simple Linear Loops* (2012), already prove that general three-variable linear-loop nontermination sets need not be semialgebraic; their Section 4 uses a diagonal positive-spectrum example. Thus the abstract matrix/guard observation is prior work, not the proposed contribution here. https://arxiv.org/html/1206.0232v1

Ouaknine and Worrell, *On Linear Recurrence Sequences and Loop Termination* (2015), Example 3.1, discuss the closely related irrational-rotation cone for non-strict guards. Strictness removes orbit points from the limiting circle in this construction. https://www.cs.ox.ac.uk/james.worrell/lrs5.pdf

The signal-machine model, geometric multiplication/division gadgets, and conservative stacks are established. The authors' overview explicitly describes geometric counter encodings and multiplication/division. https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/AGC/intro_AGC.html

Repository overlap checks read the finite-schema volume README and independent review copied in the Report56 source packet, and searched the live connected repository for `signal rotation`, `non-semialgebraic`, `periodic collision`, and `conservative stacks`. Search results were pinned to commit 7ba8f64e6a2598fde7476cb6759702f677c4bf3a; the source packet's inert copied reports are at e3e58a8820593857650bb7a0193a11ec32db67d6. These bounded checks found no same five-signal periodic construction, but do not establish literature priority. No priority claim is made.

## 7. Stronger sign-test obstruction on rational and integer encodings

The accepted points {R^k p:k>=1} and rejected points {R^(−n)p:n>=0} are disjoint dense rational subsets of the same critical circle. Their disjointness follows from R's infinite order. A finite polynomial-sign formula, with even arbitrary real coefficients, restricts to a semialgebraic subset of the circle, hence cannot classify both dense subsets correctly. Thus no finite polynomial-sign formula agrees with the validity predicate on all rational gap inputs.

This also rules out a finite polynomial-sign formula only on positive integer gap triples; that extension needs an argument because a putative formula need not be homogeneous. For each polynomial f in such a formula, split f into its finitely many homogeneous parts. On the ray t g, its eventual sign as t tends to +infinity is determined by the largest-degree nonzero homogeneous part at g, or is zero when all parts vanish. Replace every atom by this finite Boolean sign description. The resulting eventual-ray formula is semialgebraic. For rational g, infinitely many positive integer multiples lie in the integer domain. Physical validity is constant on that positive ray, so agreement at all those integer multiples forces the eventual-ray formula to agree with validity at g. This contradicts the dense rational accepted/rejected subsets above.

The conclusion concerns formulas without integer-quantified witnesses. It does not rule out Diophantine representations; the elementary rational membership algorithm in Section 4 establishes a recursive predicate, hence an existential-natural Diophantine representation exists by MRDP.

The threshold is a section-dimension threshold: the five-live-signal collision section has three free positive gaps. The scale-normalized slice has two affine coordinates, but introducing its constant baseline is precisely the third homogeneous coordinate. It does not contradict the two-dimensional homogeneous classification of Report56. Combined with that report, the construction establishes a sharp four-versus-five population boundary for universal semialgebraicity of this fixed-complete-macro input class, not a decidability threshold for arbitrary signal-machine behavior.
