# Independent review: eta-zero graph adapter

No concrete mismatch was found in the displayed prototype or its stated
proof boundaries. Independent reconstruction confirms that the prototype
removes exactly the `eta=n_eta+1` node and replaces its consumers with
`n_eta`, preserving every other row and the input/port order. This gives the
stated forward valuation correspondence, not the converse zero map. The
author's static receipt reproduces.

The independent check evaluates the actual prototype at 350 exact integer
valuations, including eta zero and cases with negative signed C, against all
of the displayed intermediate values and all four factors. It also exhausts
the relevant mod-four classes for each factor. These bounded calculations
support the displayed algebra and the existing integer unit argument; they do
not supply the required formal unit-factor proof in an arbitrary model.
In particular, the actual main carrier is
`U*(X+a*c)+H*(U*gamma+R+1-k)` and has **no `X*Y*q` term**.

The `P72Early.early` source has an explicit `q=3*t+2` premise and a carrier
with `S=4Yq`, `M=Sq`, and the additional term `S*X`. The prototype supplies
neither that congruence premise nor this carrier as stated; rescaling its
actual balance does not manufacture the extra summand. Similarly the
`FreeJMainCongruence` source includes the distinct `E*q` term. Their use
requires a separately justified adaptation, exactly as the audit says.

This review does not establish eta-zero impossibility, graph-zero maps,
port/model casts, provider compatibility or an iPRA endpoint. It does not run
Lean or builds. The deterministic check pins the actual audited sources and
its own finite checks; reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta-zero-graph-adapter-independent/check.py | cmp - reviews/ordinary13-eta-zero-graph-adapter-independent/result.json
```
