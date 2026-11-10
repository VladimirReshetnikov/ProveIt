# Sign20 port-dependent square coefficients: failed first attempt

Author-observed outer session `20252` exited 1. The first three ingredient
stages compiled, but the fourth stage failed both proposed coefficient proofs:
ring normalization retained `MvPolynomial.C` terms distinct from integer casts.
Both failed theorem reports include `sorryAx`; no square coefficient theorem
or object is claimed, and final postflight was not reached. The [independent failure audit](../../../reviews/nine-sharing-sign20-leading-coeff-failure-independent/README.md) passed; the packet is frozen.
