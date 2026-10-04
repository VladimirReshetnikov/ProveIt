# Exact raw-interface hardness review

Date: 2026-10-04. Read-only primary-source and interface analysis. No upstream scripts, schedules, or messages to third parties were executed. No new polynomial, counts, novelty claim, or article is produced.

## Verdict

**Yes, at the computable many-one reduction level.** The ordinary target-firing language with the exact supplied physical input is recursively enumerable complete, using Cairns' published vertex-prediction construction with the elementary endpoint corrections explained below. Neither signed/negative perturbations, unbounded per-site initial heights, nor infinitely repeated firing of the target is required.

This gives hardness for the full varying-tile interface and for some fixed stable periodic tile with variable finite patch and exactly encoded translated target. It does not identify that fixed tile with Report35's frozen tile. It does not provide an executed or arithmetically costed raw-program compiler. Transfer to the submitted repeated-firing polynomial remains conditional on that certificate's separately audited exact semantic equivalence.

## 1. Relation being classified

Let L consist of valid positive integer physical codes whose decoding yields:

- positive periods p,q,r and a base-32 finite tile T with pqr digits in 0 through 5
- positive patch dimensions d,e,f and a base-32 finite patch D with def digits in 0 through 15, supported at [0,d)×[0,e)×[0,f)
- three zigzag codes for one specified signed target v in Z³
- an ordinary finite legal threshold-six toppling sequence containing v, with repetitions allowed

The eleven fields are paired exactly as prescribed by the submitted interface; malformed inputs are outside L. Declared zero padding is permitted. Every initial height is between zero and twenty, but subsequent heights and firing multiplicities are unrestricted.

## 2. Exact normalization of a hardness instance

Take the finite-perturbation vertex instance supplied by source anchor §4. Write its stable periodic background as b, its finitely supported nonnegative seed function as δ, its periods as P1,P2,P3, and its distinguished alarm vertex as a. The published event is the first firing of a, not finite stabilization and not recurrence.

The hardware uses finite stable primitives. An input wire may be provided with an isolated interior height-five seed site. Adding one chip activates that wire. Reserve different sites for different directly activated logical wires; a longer wire segment suffices and is a fixed finite adjustment. Consequently the finite initializer can use δ values only zero and one. This is an interface inference from the wire activation rule, not a claim that the paper prints the patch radix. Even retaining two chips at a designated input would stay below fifteen.

Let S be the finite support of δ. For each coordinate i choose

    si = Pi · max(0, ceil(−min{u_i : u in S}/Pi)).

For an empty support use the minimum zero. Define

    δ'(w) = δ(w−s),     a' = a+s.

All seeds now have nonnegative coordinates. Because each si is a multiple of its period,

    b(w−s) = b(w),     b(w)+δ'(w) = (b+δ)(w−s).

Translation is a graph automorphism preserving legal toppling sequences. Therefore a fires in the old configuration exactly when a' fires in the new one. No chip subtraction, background height increase, or new dynamical argument is involved. The supplied target must be translated; this review does not claim it remains the origin.

Choose d,e,f large enough that S+s is contained in the nonnegative patch box, using dimension one on any empty axis. Encode

    T = sum b(x,y,z) · 32^(x+p y+pq z),
        0<=x<p, 0<=y<q, 0<=z<r,

    D = sum δ'(x,y,z) · 32^(x+d y+de z),
        0<=x<d, 0<=y<e, 0<=z<f.

Encode each target coordinate h by ζ(h)=2h for h>=0 and ζ(h)=−2h−1 for h<0. Apply the declared finite Cantor pairing and positive-input offset. All operations terminate and produce exactly the requested physical code. Radix 32 introduces no mathematical restriction on the finite tile or patch because every digit fits its allocated range.

## 3. Fixed versus varying tile; computability

There are two valid levels:

1. Permit the tile to vary with the machine. The source's finite transition-rule construction yields the machine-dependent circuit and its finite periodic description.
2. Fix one universal Turing machine and one sufficiently separated finite-cell realization of its circuit, including blank initializers and alarms. Thereafter the program/input only changes its finite initial tape and the selected seed sites. Period-multiple translation above preserves that same tile. The target and finite patch may vary.

For the second, existential computable-reduction statement, all hardware dimensions, route choices, tile digits, and seed-wire offsets are finitely many fixed integers. They can be hardcoded into a Turing program. Finite tape initialization and the displayed translation/serialization are computable. The existence of that computable function does not require this review to output its enormous numeric tile or a practical implementation.

Do not conflate the one-chip, input-specific periodic-initializer variant with the fixed-tile variant: building the input into the periodic wiring makes the tile depend on the input. Fixed tile instead uses the finite list of direct seeds.

The resulting many-one map f satisfies

    machine M halts on input x  iff  f(M,x) belongs to L.

This is a theorem about an external total computable map. It does not say f is polynomial, a fixed arithmetic expression, or included among the gates/witnesses of the submitted physical-input polynomial.

## 4. R.e. membership and the exact first-firing event

Given a valid finite code, the initial height at any signed lattice coordinate is computable by modular tile lookup and bounded patch lookup. Enumerate every finite sequence of signed lattice coordinates, for example by increasing bounds simultaneously on its length and coordinate magnitudes. Check each candidate step using

    current height at v = initial height at v
                          + earlier firings at its six neighbors
                          − 6 · earlier firings at v.

Accept when a legal candidate includes the supplied target. Every test is finite, and every successful finite prefix eventually appears. Thus L is r.e. independently of any Diophantine representation.

If the target fires in a complete execution, its occurrence has a finite index and supplies such a prefix. Conversely, a legal prefix containing the target forces a positive target odometer in any complete execution by legal/complete comparison (source §§1.1–1.2). Equivalently, extend the prefix by a fair legal scheduler. No global stabilization or infinitely recurring target event is necessary. Combining membership with the reduction proves r.e.-completeness and undecidability.

## 5. Printed initializer defects and explicit repair

These are real defects in the displayed endpoint formulas and must not be silently presented as verbatim correct source code.

### Direct-seed initializer: §3.2.4, printed p.17

The context defines x0 as the minimum and x1 as the maximum of the finite set consisting of the head location zero and initially nonblank tape locations. It directly initializes every cell of [x0,x1]. Its left blank signal propagates toward smaller x, and its right blank signal toward larger x. The two listed free input wires are the left initializer in c(x0−1,0) and the right initializer in c(x0+1,0).

The second location must be c(x1+1,0). If x1>x0, the printed choice can start the rightward blank wave inside the explicitly initialized interval. In particular, when x1=x0+1 and that endpoint is nonblank, the right initializer would also assign the blank state there, contradicting the intended tape and potentially activating both members of a dual-rail bit. Starting at x1+1 instead covers exactly the right complement of [x0,x1], never any explicitly assigned cell. The left start x0−1 is already correct.

This repair is forced by the declared interval partition. It involves only computing a finite endpoint and moving a seed; it does not require deciding anything about the simulated computation.

### Alternate periodic initializer: §3.2.5, printed p.18

The source's added initialization wire in a cell with horizontal index x connects to the left blank input at c(x+x0−1,t), the right blank input at c(x+x1−1,t), and the directly initialized state wires in the translated finite interval [x+x0,x+x1].

The right connection must instead be c(x+x1+1,t). The printed minus one starts two cells to the left of the first cell outside the interval. Because the right initializer also initializes its own starting cell and all cells to its right, it reaches the right endpoint of the explicit input interval and can conflict with a nonblank endpoint. Plus one starts exactly outside that endpoint and gives the intended disjoint partition.

The fixed-tile reduction does not use this alternate single-seed variant. Its typo is nevertheless disclosed to prevent copying the alternate construction literally.

The foregoing is a mathematical correction supported by the source's own stated initialization invariant. It is not a claim that arXiv v2 has been amended or that an author-issued erratum was found. The source remains a qualitative construction, not a supplied executable coordinate compiler. If an application requires a fully paid literal compiler, this review does not satisfy that stronger requirement.

## 6. Relationship to Report35 and the repeated certificate

The pinned Report35 loader establishes a different event: its fixed U15 tape halts exactly when total sandpile activity is finite. Its sites are one-shot, and its finite initializer is nonnegative and binary. Its composition document certifies global stabilization in a fixed external prism with a binary odometer. Neither statement alone supplies a distinguished target that first fires exactly at a machine halt. One cannot infer that event merely from global termination.

For the present ordinary target-firing relation, use the published vertex/alarm construction, not an unsupported re-interpretation of Report35's frozen global-halting layout. Appending an alarm subsystem to the latter would be a separate physical construction requiring its own proof and would generally change the tile; it has not been performed here.

The repeated certificate's exact relation accepts every finite ordinary legal prefix on the declared physical input. Consequently it need not prove that a particular reduction's physical sites fire at most once. Its successful full audit would permit the implication

    exact physical-interface equivalence
    + the computable reduction above
    => r.e.-complete set of positive inputs with positive-integer witnesses.

That conclusion does not deliver a fixed arithmetic compiler from raw machine-program codes, universal-polynomial parameter substitution by arithmetic expressions, unique/finitely-many witnesses, real-witness equivalence, or new arithmetic counts. Those are separate assertions.

## 7. Remaining boundary

No unresolved negative-perturbation, height-range, nonnegative-box, exact-target, or first-firing-versus-recurrence mismatch remains at the computable-reduction level after the disclosed endpoint repair. The remaining imported mathematical ingredient is the published physical circuit simulation and its ordinary qualitative geometric realization. This review does not re-audit every infinite routing separation claim or implement its coordinate compiler. It also does not certify the submitted polynomial audit, which is independent work.

Primary anchors and short compliant quotations are in PRIMARY_SOURCE.md. Local source identities are in SOURCE_PINS.json.
