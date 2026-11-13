# Same-valuation model transport binding for free-J

`graph_z_of_model_transport` proves in an arbitrary `IΣ₁` model that the
actual free-J graph expression `Z` at a specified valuation equals `M·τ` in the
model difference ring. Its explicit assumptions are:

- The natural numbers satisfy `1≤q` and `C+F+α=q`.
- The same graph valuation has coordinates `F,α,X,Y,r,η,ζ` at slots
  `1,2,5,6,7,8,9`, respectively.
- The actual integer ports satisfy `ι(J)·(β:DiffRing V)=ι(q−1)` and
  `(K_port:DiffRing V)=ι(K)`; `J` is graph coordinate 0. These are hypotheses,
  not a proof identifying the fixed large integer ports with the symbolic
  compact coefficients.
- The model-natural equations are
  `(qK+X)C=qF+(q−1)(qz)` and
  `M(ell+k+r)+Y(q−1)=Mτ+(1+(q−1)k)q³((q−1)(qz))`, where
  `M=q³(q−1)`, `ell=XY²k`, and `k=η+ζ`.

The proof maps the natural equations into the difference ring, derives the
actual graph `M`, `ell`, and `Bt=(q−F−α)(X+Kq)−qF` at this **same**
valuation, and applies the checked additive first-transport identity. It
assumes all coordinate and port bindings, transport equations and the given
natural witnesses. It does not itself construct positive `r` or a graph
valuation, identify the enormous fixed ports with symbolic constants, establish
the other graph factors, or produce an iPRA proof.

The bounded author attempt 03 exited 0 in 7.429 seconds with no warning or
`sorryAx`. Source SHA-256 was
`9f42cfe77f737bb8bc9e95763d2a0bca4fe6e23baa07ebe44d5db0c4a87d85c6`;
object `/tmp/free-j-model-transport-binding-author-5f_wn1t5/FreeJModelTransportBinding.olean`
had SHA-256
`333514f2c4ad2d85ad3918448438952a0e908607faf05b58f3e4458bd1c05eb5`.
All three provider overlaps were compared byte-for-byte, and 1,181 live
provider files and direct/named transitive bridge companions remained unchanged.
This is a single-author compile, not an independent replay or an audit of
inherited provider ancestry, package-transitive, or dynamic dependencies.
Lean reports `propext`, `Classical.choice`, and `Quot.sound` as metatheoretic
dependencies.

Attempt 01 failed on local coercion and ring normalization issues; attempt 02
elaborated but the runner rejected a style warning. Their source and logs are
retained; attempt 03 removed the warning without weakening the theorem.
