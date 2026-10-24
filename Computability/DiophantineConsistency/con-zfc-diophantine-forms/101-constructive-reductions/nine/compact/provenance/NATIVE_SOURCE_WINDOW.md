# Literal old-z source to the native arithmetic window

`NativeSourceWindow.source_native_window` now derives the forward arithmetic
window from every positive zero of `SplitCertificate59.sourceRows`. It proves
the exponential and mask semantics; no window or decoded-mask hypothesis is
supplied by the caller.

Write `q=1+beta*J`, `C=q−F−alpha` and `R=(c*j−V).toNat`, in the original
31-coordinate source order. For the coefficient interface below, the theorem
produces `N>0` and proves

```
B=2^d, q=B^N, J=1+B+...+B^(N−1),
C>0, C+F+alpha=q,
(C−1) AND (MC*J+1)=0,
F AND (MF*J−1)=0,
sigma_2(R)=3dN+2,
w=2^(R−dN),
(K+w)C=F+(z−1)(q−1).
```

The transport retains the original positive old-z coordinate. Its `z−1`
may equal zero; the proof does not silently require a positive shifted
coordinate. All natural subtractions are justified by source bounds.

`NativeSourceMask.Interface ports d MC MF` states exactly:

```
d≥4,
ports0=2^d−1, ports1≥0,
ports2=MC, ports3=MF+ports0,
MC<2^d−1, MF<2^d−1,
MC even, MF=4(mod8),
sigma_2(MC)+sigma_2(MF)=d.
```

The fourth port is shifted once. These are arithmetic coefficient
conditions, and do not make an arbitrary `K` an instruction-tableau encoding.
The whole fixed native tuple must still be bound to the intended coefficient
recipes before a machine interpretation can be concluded.

The source-to-mask proof closes the remaining local binding from
[NATIVE_HALF_BINOMIAL.md](NATIVE_HALF_BINOMIAL.md). It derives `q=B^N` and the
exact source multiplier `J`, proves the integer four-block rank identity,
justifies every complement and decrement, and computes the populations of
the two repeated masks. The half-binomial lower bound saturates the general
population upper bound, forcing the two masked overlaps to vanish. No
carry-free assumption is used to establish that saturation.

All public interfaces in `NativeSourceMask` and `NativeSourceWindow` have
dedicated axiom audits using only `propext`, `Classical.choice` and
`Quot.sound`.

The next soundness contract is concrete: specialize the **whole** native
tuple, decompose `K=DC+B*DR`, and prove that the displayed arithmetic window
decodes to a marked tiling for its literal Wang language and hence to a K215
blank halt. The converse needs canonical tiling/padding witnesses and the
ordinary Pell construction. Those unbounded contracts and the internal ZFC
biconditional remain open; none is asserted by this forward arithmetic
theorem.
