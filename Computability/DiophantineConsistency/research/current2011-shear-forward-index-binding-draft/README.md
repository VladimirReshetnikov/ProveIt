# Forward 71/60 index bound: proposed source composition

This is an **unelaborated source-only client**, not a checked Lean theorem or
a completed 72/46 zero map. It proposes deriving the natural `2*R<c` bound
and the positive scalar gap from the *actual positive-shifted 71/60 zero at
one valuation*. No independent norm, rank or scalar oracle is a premise of
that proposed natural theorem. Its separate difference-ring corollary keeps
the exact rank and c cast equalities as explicit hypotheses.

The proposed path, at `w j = v j + 1`, is:

1. `OrdinarySphere7160Model.sameZero94` transports the 71/60 zero to a
   67/94 zero at the **same** shifted valuation, then the positive-shift
   lemma supplies an unshifted 67/94 zero at w.
2. `ArithmeticCarrier94Extraction.current94_equations w` supplies its five
   natural transport/norm equations. `ArithmeticCarrierSoundness2011.current_bounds`
   supplies the actual current port bounds.
3. `ArithmeticCarrier94Indices.ordinary_first_indices` consumes those five
   equations and positive coordinates and returns `2*rank(w)<c(w)`.
   `ArithmeticPellFirstIndex.scalar_window` applied to the same transport
   equation returns `0<q(w)−w(1)−w(2)`.

All theorem names, signatures and selected source bytes are pinned in the
[checker](check.py). The code follows the existing explicit application in
`ArithmeticCarrier94Soundness.population_of_ordinary`, but proof-term
elaboration, import/provider compatibility and tactic behavior have not
been tested. The original graph-to-syntax and current-port caveats in the
71/60 model join remain inherited.

## The still-explicit cast cut

The source theorem's rank uses natural truncated subtractions `q−1`,
`q−F`, and `q²−1`; the shear order lemma uses the corresponding signed
`Carrier65.core` fields in `DiffRing V`. The proposed `ring_half_of_casts`
therefore assumes, rather than claims to have proved,

```
(core currentP shiftedRing).rank = iota (ArithmeticCarrierRadix2011.rank w)
(core currentP shiftedRing).c    = iota (natC w).
```

It then transports the natural strict inequality through `iota_lt_iota`.
The positive gap from the preceding theorem is the relevant route to
`F<=q`; the other natural subtraction bounds follow from `q>=1`. The
port casts and these subtraction equalities must still be formalized at the
same valuation; this draft does not discharge either equality. Likewise,
the extraction of the auxiliary unit norm and positive model-natural shear
witness, literal child evaluator, reverse map, final no-zero equivalence,
and iPRA/Gödel–Gentzen clients are separate obligations.

Run the bounded, read-only source audit from the DiophantineConsistency
directory:

```
python3 -I -S -B research/current2011-shear-forward-index-binding-draft/check.py > /tmp/shear-forward-index.json
cmp /tmp/shear-forward-index.json research/current2011-shear-forward-index-binding-draft/result.json
```

It checks source pins, exact interface markers and explicit cast premises;
it does not parse Lean, launch Lean or build anything, replay any theorem,
or authenticate transitive providers.
