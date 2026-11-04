# P65 halt-side extra positive coordinates

`P65HaltPositiveCoordinates.lean` proves three all-model lemmas for a model
`V` of IΣ₁ (and hence for any stronger model to which the existing model
machinery applies):

* `rep_index_positive`: if `N ≥ 2` and `rep d N = 3*j+1`, then `j > 0`;
* `halt_length_ge_two`: `power 581197 ((2*T+3)+1) ≥ 2`, the canonical
  halt-length expression used by `CompactHaltPackedWord`;
* `shifted_exp_positive`: if `2*u < R`, `q > 0`, `w = exp(R-u)`, and
  `X = q*w`, then `X-q > 0`.

The intended application is to the two additional P65 coordinates `j` and
`X-q` in the canonical P72 halt construction. These lemmas alone neither
construct a P65 zero nor establish an internal proof in iPRA.

Checked with the captured provider, not a clean build of the current source
tree:

```sh
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/p65-halt-positive-coordinates \
  research/p65-halt-positive-coordinates/P65HaltPositiveCoordinates.lean \
  -o /tmp/P65HaltPositiveCoordinates.olean
```

The command completed with exit status 0, no warnings, and `#print axioms`
reported `[propext, Classical.choice, Quot.sound]` for each theorem. Source
SHA-256: `bfcecea98a254434a6bacd611e39fa99f0ef19857b5fd2150fdeae44c907802c`.
The resulting local object SHA-256 was
`f3a73c566b7099bb54f026d3658086efe14f1132407f210a186ef1ee623328f2`.
The external provider must be rebuilt from matching current sources before
these checks are represented as a current-source verification.
