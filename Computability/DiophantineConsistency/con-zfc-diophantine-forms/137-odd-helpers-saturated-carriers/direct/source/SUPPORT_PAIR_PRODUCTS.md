# Two support-pair products on the complete fused-nine body

Four scalar predicates can be replaced by two quadratic product predicates,
while fixing the entire accepted fused-nine body and every other witness.
This is an ordinary equivalence proposal. No source, program, projection,
equation, coefficient census or Lean artifact is produced here.

The literal parent is `research/signed-pell-cap-nine-factor-source`, sealed at
`845bc6642212eb600d2f0ecf663cb805a6e1989b63faf7087d44142e5cc75190`.
`SOURCE_PINS.json` pins the whole relevant source/ordinary inputs;
`BINDING.json` records the actual rows, graph records and complete private
occurrences. All indices below belong to this sealed parent, before projection.

## 1. Exact exchange and elementary sign lemma

Keep all 406 body coordinates and 341 body rows. Remove only these graphs:

| Predicate | Actual parent row | Entire private triple |
| --- | ---: | --- |
| v183 >= 0 | 345 | 418,419,420 |
| v184 >= 0 | 346 | 421,422,423 |
| v191 >= 0 | 348 | 427,428,429 |
| v192 >= 0 | 349 | 430,431,432 |

Replace them by two fresh private Legendre graphs, with disjoint triples:

    v183*v184 = a0^2+b0^2+c0(c0+1),               (G0)
    v191*v192 = a1^2+b1^2+c1(c1+1).               (G1)

Each predicate is directly quadratic. No new body product gate is required.
The embedded cap graph, strict fused ninth-factor graph, helper graph and
every other graph remain exactly as in the parent. Each discarded auxiliary
occurs only in its own discarded row. The fresh triples occur only in G0/G1
and are outside the frame, powers, cap, pool and native semantic ports.

For integers u,v and a positive integer q, the two conditions

    uv >= 0,       qu+v > 0

imply u,v >= 0. If u<0, then uv>=0 implies v<=0 and qu+v<0. If v<0,
then uv>=0 implies u<=0 and again qu+v<0. This allows zero factors and
therefore uses uv, not uv-1, in the graphs.

## 2. Recover both denominator powers before either pair sign

The proof does not invoke the entire accepted fused-nine theorem with four
of its hypotheses missing. Instead it repeats only the abstract signed cap
and signed-scale request lemmas, whose premises are independent of these
four signs, and then restores all four old predicates before invoking that
theorem.

Write t=v0+16, B=v5, q=v179, L=v181, Qt1=v189, A=v246 and W=v245.
Retained scalar guards on v0,v7,v8,v185 and exact rows3/167 give

    t >= 16,    B=v7+v8+1 >= 1,    q=B+v185+1 >= 2.

No assertion about L, Qt1, F, x, y, K or N is needed at this stage.
The unchanged row333 is W=2(2+sum37 actual atoms^2). Its atoms include t,
t+1, q, L and Qt1. Thus W>=516 and their absolute frame bounds hold
without any sign for the four removed coordinates. The frame scale
rows202..204 and retained v247>=0 give a=|A|>=(W+1)^W and
|A-1|>4W^3. The primary norms, quadratic cap row217 and primary-only pool
row218 are unchanged. The helper comparison v255-4>=0 can be normalized
temporarily by the accepted reflection of 251/252/254/375; it fixes every
removed target, G0/G1, every frame atom and every body power port.

The complete signed-target cap theorem therefore applies with t as its sole
known nonzero target. Its assumptions use only the frame, normalized helper,
cap, primary-only pool and primary norms. They do not use 183/184/191/192
or the sign of L/Qt1. It yields

    v258=Y_t(A),       v257=+/-X_t(A),

and the other fourteen canonical signed-index ordinates. No all-positive
index ledger or native factorial/binomial semantics has been assumed.

Now apply the actual q-base call4 at row253, whose pair is257/258 and whose
output is L. At 1<=t<W, 2<=q<W and |L|<W, the signed-scale request lemma
orients v257=X_t(A) and proves L=q^t even when L was initially signed.
For completeness, put T=2Aq-q^2-1 and H=X_t(A)+(q-A)Y_t(A). The literal
lowering gives L=H modulo T in the canonical branch, while the opposite
branch gives L*q^t=-1 modulo T. The frame bounds turn both congruences
into equalities. The latter is impossible because q^t>=2 cannot divide1.
This argument uses neither output positivity nor F>=1.

The exact signed t+1 recurrence at rows259..266 then uses this oriented
pair. With X=X_t(A), Y=Y_t(A), it constructs

    Xnext=A*X+(A^2-1)*Y,    Ynext=X+A*Y,
    Qt1=Xnext+(q-A)*Ynext modulo T.

The recurrence identities give Xnext=X_(t+1)(A), Ynext=Y_(t+1)(A).
The same absolute frame bound therefore gives Qt1=q^(t+1). Its complete
lowering and all shared gate/modulus rows are recorded literally in the
binding. Neither191/192 nor their desired signs occur in this lowering.

## 3. Restore four old predicates on the original body

The two unchanged rows166/171 state exactly

    q*v183+v184 = L-2 = q^t-2 > 0,
    q*v191+v192 = Qt1-2 = q^(t+1)-2 > 0.

The strict inequalities use q>=2,t>=16. G0/G1 give the corresponding
nonnegative products. Section1 therefore restores all four scalar signs.
All these coordinates are fixed by the temporary helper reflection, so the
signs hold on the original unnormalized input assignment.

Given a zero of the new system, keep its entire original406-coordinate body,
h, signed A/C and every other retained graph witness. Discard the two fresh
triples. Choose four fresh old Legendre triples for183,184,191,192 at their
old private positions. Every complete old row then vanishes. Only now invoke
the accepted full fused-nine theorem and its whole coherent native calibration.

Conversely an old zero already has all four scalar signs, hence both products
are nonnegative. Keep the same whole body and all other witness values,
discard the four old triples and choose two fresh triples representing the
two products. This gives a new zero. No old triple is reused for a different
integer. The maps are existential witness maps, not a bijection between
three-square representations or an equality of whole SOS polynomials.

Thus the two exchanges are simultaneously valid at every complete body tuple,
and ordinary soundness and positive completeness transfer through the exact
parent calibration. The change is confined to private guard witnesses.

## 4. Boundary and other retained anchors

The exchange replaces four graphs by two with no new body gates. It has no
measured projected dimension, degree/height/term census or optimizer claim.
A future materialization must independently bind the complete compacted
coordinate/row maps, privacy, ordinary calibration and actual full quartics.

The x/y support pairs213/214 and225/226 remain intact here. Their positive
weighted-output anchors establish the signs of the initially unknown x/y
indices in the accepted chronology; they do not have the already-positive
t and t+1 indices used above. Likewise the factorial pair7/8, the q slack185,
the frame guard247, the aggregate guard174, the existing interval products
and the strict ninth-factor graph are unchanged. No claim that these other
predicates are indispensable or independently removable is made.
