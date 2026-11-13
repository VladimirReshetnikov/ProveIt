# Independent source review of the explicit Pell-period draft

The proposed specialization matches the retained `doubled_quotients` theorem's type, hypotheses and argument order. Its algebra and rewrite directions are consistent at source level, including the `m=0` case. No concrete missing model assumption or Lean source defect was found. The draft remains **unelaborated**: source inspection and finite controls cannot establish that the tactics compile, that its imports resolve to authenticated providers, or that the theorem yields a proof-existence statement in the chosen iPRA encoding.

The existing result assumes the same `ORingStructure V` and `IΣ₁` model instances as the client. Substituting `n=ycoord m a` and `R=m` gives the index `2*ycoord m a*m`; the client first rewrites `2*m*ycoord m a` into that order. The abscissa equality is then exactly the existing `hx`. For the ordinate, write `c=ycoord m a` and `d=xcoord m a`. The existing `hy` gives

```text
2*c*d*c + c*c*s = (2*d+s)*c*c,
```

so the proposed natural-model witness `t=2*d+s` is correct. The imported recurrence itself imports the ring tactic, and existing nearby arbitrary-model sources use `ring` for analogous commutative arithmetic. This is source evidence for tactic availability, not an elaboration test. The second rewrite uses `<;> ring`, so it also tolerates the preceding rewrite closing the goal; the first branch's `exact hx` is appropriate after the stated index rewrite.

The recurrence's multiplier is `a+2`, and its `delta=(a+1)*(a+3)` is the corresponding `(a+2)²-1`. The source theorem already includes zero index; in that case `c=0`, the index is zero and the displayed two equalities reduce to the recurrence's initial values. `time_le_y` gives a route to `c>0` when `m>0`, but the present draft does not construct the positive quotient, identify a literal graph ordinate with this recurrence, establish a parent auxiliary witness, or encode an internal proof.

The independent checker pins the draft and its source interfaces, checks the exact theorem statement and client instantiation, verifies the commutative index and coefficient identities as sparse polynomials, and tests bounded integer recurrences including index zero. Those controls do not establish the quantified model theorem independently of the existing theorem or validate Lean tactics. The existing source uses local irreducibility annotations for represented coordinates in other contexts; the client's omission is not an identified error, but its elaboration/performance remains untested.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-explicit-pell-period-model-independent/check.py | cmp - reviews/ordinary13-explicit-pell-period-model-independent/receipt.json
```

No Lean, build, staging, provider audit, axiom inspection or proof-existence result was performed.
