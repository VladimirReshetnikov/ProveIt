# Independent review: nonnegative fixed-port boundary zero

**PASS.** For both fixed choices `J=1,2`, take `q=beta*J+1`,
`K=q−1`, and keep the actual fixed compact beta and mask ports. Assign
`F=z=w=t=f=i=T=y=zeta=1`, `alpha=q−2`, and `s=eta=h=0`.
The fixed beta is `2^590069−1`, so the remaining coordinates and both K
values are positive. The three displayed zero coordinates violate the
strict positivity required for an admissible graph witness.

Directly in the generated graph, `Y=U=ell=c=a=0`, `H=Delta=3`,
`k=1`, `A0=Na=1` and `M=W=Lt=0`. The output is therefore exactly zero.
This identity does not depend on either mask or the rank value.
The independent [checker](check.py) parses all 72 Lean graph gates and
evaluates them symbolically in `ℤ[beta, low, high]` for both J cases;
it checks every identity listed above and the exact output zero. It ran
with exit 0 and retained [result.json](result.json). This is an exact
polynomial identity check, not a finite sample, although it is not a Lean
theorem. The author's checker also ran with exit 0 and its output was
byte-identical to its retained result.

The positive all-moduli assignments use the same fixed ports and vector,
except that the three zero coordinates become `N`. For any prime `p`,
choosing `N=p^r` makes those coordinates converge to zero in `ℤ_p`, while
all other coordinates stay fixed. Thus the assignments are compatible
modulo increasing powers and converge to this exact boundary zero. This
observation gives no strictly positive integer solution and does not decide
other p-adic arguments, constraints at unbounded precision, or the
existential reverse implication. The separate [all-moduli audit](../p64-qcube72-fixed-mask-all-moduli-independent/README.md)
checks the strictly positive finite assignments and actual mask recipes.

Reviewed construction SHA-256: README
`b788bb78ee249dcbaa5f23c4a2a8097d97be911c76291bdba26df75bf5e3277d`,
checker `ab5351c3471d1960c12aedb1cc27b94f0c9e39250f3cfe0417c1ab60052fa782`,
result `a7444e05d2be20fdbacc42d6ca3aa050113c94f6d3ada0151dc6d2d382216c1f`.
Independent checker SHA-256
`97ccc54cc27403953e6f5fa4e7220518fee73d38c91f8cf4402fd5d7583097d5`,
result `e837d86817ed1149854dcb469ad06119244515c672c15179a37a34d8eb97d008`.
