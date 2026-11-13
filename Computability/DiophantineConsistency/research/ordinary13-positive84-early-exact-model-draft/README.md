# Proposed direct positive-84 early and exact indices

This unelaborated source draft narrows the `ExactPowerGraphCut` needed by the
direct 84 power proposal. It does **not** prove either remaining graph cut,
Lean elaboration, provider/axiom provenance, or an iPRA endpoint. It never
uses 84→83 or assumes `q | X`.

The two separately generated 84 graph outputs are proposed definitionally
equal. On a positive 84 zero, the independently drafted `Unscale84LargeK`
client supplies a natural first norm at the actual 84 first residual. Given
represented positive beta and explicit rank lower bound, rank window and
signed q⁴ rank congruence, `early_of_rank_facts` proposes the existing
natural-first-norm index wrapper at that very valuation. It returns n,w
with n≥13, the actual first Pell ordinate, exact k decomposition and
`(2n) mod q⁴ = R+1`. The initial result is a congruence, not an exact index.

`MainStrongAux` specifies the remaining same-model, same-main-index data:
main x and y coordinates, main norm, strong norm, direct-auxiliary equation
with a natural witness, and the actual **extra `X*Y*q`** oriented balance.
Together with the early n,w and rank window, `exact_of_facts` proposes the
existing `P72Exact.indices_ordinary` wrapper. It obtains `m=R` and
`2n=R+1`, then constructs `ExactPowerFacts` with the same main root and first
quotient w. The final main balance is not replaced by the no-extra-term
prototype's balance.

`rank_congruence_of_main` further proposes deriving the q⁴ congruence from
that explicit extra-term oriented balance, using the literal `Y=q³*s` and
`FreeJMainOrientation.rank_congruence_from_main`. Its auxiliary 12-slot
tuple is merely an arithmetic argument to that theorem; no 12-input graph
zero is assumed. The exact expression retains `X*Y*q` throughout. The last
client therefore assumes only two all-model graph cuts:

* `RankWindowGraphCut`: the actual natural rank is at least 26 and satisfies
  the compact window. Binding the signed graph rank to that natural
  expression and proving the compact gap and port bounds remain work.
* `MainStrongAuxGraphCut`: the 84 zero supplies the explicit same-index main
  root, its positive orientation and balance, and the strong/auxiliary norm
  witnesses. Extracting and identifying those witnesses from the 84 graph
  remains work; no original literal-zero premise is silently imported.

All source clients, including `same84`'s definitional equality and the
arithmetic tuple casts, are unelaborated proposals. The first/main norm,
early-index, exact-index, compact beta, signed-magnitude and positive-model
provider chains still require compatible Lean builds and axiom inspection.
From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive84-early-exact-model-draft/check.py
```

The read-only checker pins direct inputs, compares graph row strings and
source signatures, and evaluates bounded synthetic oriented-balance and rank
congruence controls. These controls are not full graph zeros and do not
verify Lean or arbitrary-model facts.
