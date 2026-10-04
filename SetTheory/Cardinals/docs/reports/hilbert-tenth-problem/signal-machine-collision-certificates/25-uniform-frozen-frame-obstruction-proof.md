# Original-frame untimed reachability: a reversible obstruction

## Proposition

There is a globally reversible, number-conserving binary cellular automaton F, with F and F^{-1} of radius at most 91, whose forward untimed reachable-output set from the single fixed input C_13 = {0,5,6,13}, encoded by its four sorted absolute occupied coordinates, is not Presburger-definable. Its singleton-stationary version has a Presburger-definable untimed reachable-output set from the same input.

This is a direct corollary of the approved reversible clock and its complete orbit in Report 49, not a new local-rule construction. It supplies an obstruction for the original-frame question in Report 51, Section 11, item 4; it does not classify all rules or phase drifts.

## Construction and complete orbit

Call the radius-at-most-90 clock of Report 49 G (the report itself calls it F). For D >= 13 set C_D = {0,5,6,D} and L_D = 2D-22. Report 49, Proposition 4.1, gives every integer-time state in one cycle:

- G^s(C_D) = {0,5+s,6+s,D}, for 0 <= s <= D-11
- G^s(C_D) = {0,2D-18-s,2D-14-s,D+1}, for D-10 <= s <= 2D-23
- G^{L_D}(C_D) = C_{D+1}

The first two ranges are disjoint and cover 0 <= s < L_D. In both ranges the displayed coordinates are strictly increasing: the middle pair is at least 5 sites right of the origin and at least 5 sites left of the rightmost particle. Thus the minimum occupied coordinate is always 0, and neither spectator can change the ordering or impersonate a middle particle. All singletons are fixed by G, since each literal rule endpoint requires at least two particles.

Let tau_a translate every occupied site a units to the right and define

    F = tau_1 composed with G.

Translation commutes with G. Hence F^t = tau_t composed with G^t for t >= 0; F^{-1} = G^{-1} composed with tau_{-1}. Translation and G are full-shift reversible binary CAs fixing vacuum and conserving finite particle number. The radius bounds of F and F^{-1} are at most 91. A singleton moves one site right per F step, so the canonical stationary-singleton frame of F is exactly G.

Starting from C_13, cycle k has D = 13+k and starts at

    t_k = sum_{j=0}^{k-1}(2(13+j)-22) = k^2+3k.

Since t_k increases to infinity, every t >= 0 belongs to exactly one half-open cycle t = t_k+s, 0 <= s < L_{13+k}. At that time the minimum occupied coordinate of F^t(C_13) is exactly t.

## Exact slice and non-Presburger conclusion

Define the forward untimed set of complete outputs

    R_F = {(y_1,y_2,y_3,y_4) in Z^4 : y_1<y_2<y_3<y_4
           and {y_1,y_2,y_3,y_4} = F^t(C_13) for some t in N}.

Intersect it with the Presburger slice

    S: y_2-y_1=5 and y_3-y_1=6.

In a right phase the two differences are 5+s and 6+s, so S holds exactly when s=0. In a left phase y_3-y_2=4, whereas S requires y_3-y_2=1, so S never holds. The complete-orbit formula and strict ordering rule out all other possibilities, including contacts, cycle endpoints and spectator substitutions. At D=13 the left phase consists of the single state {0,5,9,14}, which also fails S. Half-step states are irrelevant because one step of F uses the complete fixed composite rule.

Consequently the exact intersection is

    R_F intersect S
      = {(t_k, t_k+5, t_k+6, t_k+13+k) : k in N}.

If R_F were Presburger-definable, closure under intersection and coordinate projection would make

    {y_1 : (y_1,y_2,y_3,y_4) in R_F intersect S}
      = {k^2+3k : k in N}

Presburger-definable. A unary Presburger set in N is eventually periodic. This infinite set is not: its successive gaps are 2k+4 and tend to infinity. More explicitly, if T and P>=1 were an eventual-periodicity threshold and period, choose k with t_k>=T and 2k+4>P. Periodicity would require t_k+P to belong to the set, but it lies strictly between consecutive elements t_k and t_{k+1}. This contradiction proves the proposition.

Equivalently, the affine map (y_1,y_2,y_3,y_4) -> (y_4-y_1-13,y_1) sends the slice bijectively to the quadratic graph {(k,t): k>=0, t=k^2+3k}. The unary projection argument above is enough; no general theorem about polynomial graphs is needed.

## Fixed input, uniform relations, and the frame distinction

The failure already occurs in the four-output-coordinate relation for the fixed, anchored input C_13. Therefore a uniform original-frame reachability relation in input and output coordinates cannot be Presburger-definable either: specializing the input coordinates to (0,5,6,13) would give R_F. This implication is from the fixed-input counterexample to failure of uniform definability, and needs no uniform parametrization assumption.

For comparison, the complete untimed orbit of G from C_13 is exactly the following Presburger union:

    {(0,p,p+1,D) : D>=13, 5<=p<=D-6}
      union
    {(0,q,q+4,E) : E>=14, 5<=q<=E-9}.

For the right family use D=13+k and s=p-5. For the left family use D=E-1 and s=2D-18-q; the displayed bounds are precisely the two phase ranges. Thus this example directly exhibits a semilinear stationary-frame orbit becoming non-semilinear after reinstating a uniform drift. The stationary-frame theorem is unaffected: dropping time before or after adding a time-dependent translation are different operations. Absolute output positions are essential. Quotienting outputs by arbitrary translation removes this particular obstruction.

All reachability statements here use forward times t in N. No assertion about the union over negative times is made. The argument is unconditional relative to the already proved local-rule and orbit statements of Report 49; it does not depend on the conditional uniform-chart imports in Report 51.

Optional threshold consequence: Report 49's inherited mass-at-most-three theorem makes the complete original-frame timed evolution Presburger-definable for every fixed input with at most three particles. Projecting away time therefore makes fixed-input untimed reachability Presburger-definable there. Combined with the proposition, four is the sharp particle threshold for failure of fixed-input original-frame untimed reachability, also in the globally reversible binary class. This consequence uses that explicitly identified lower-bound theorem, not only the clock orbit.

## Sources and verification boundary

Read-only mathematical sources used:

- /workspace/shared/reversible-four-particle-clock-20261004/candidate-specification.md
- /workspace/shared/reversible-clock-report49-release-20261004/manuscript/report49.tex, Sections 2-5 and the inherited mass-at-most-three theorem in Section 6
- /workspace/shared/uniform-particle-report51-release-20261004/manuscript/report51.tex, original-frame coordinate formula and the original-frame untimed open question

Exact SHA-256 source pins are recorded in source_pins.json. The Report 49 manuscript pin is c78133175cca8be54cbf230af1423b77b0ee3bcf6d71bd816f6478800ccf9056.

No upstream executable was run. The adjacent independent_check.py was newly written from the six literal endpoint rows. Its finite checks supplement the all-time argument and do not prove the full-shift theorem. No article, novelty, or priority claim is made.
