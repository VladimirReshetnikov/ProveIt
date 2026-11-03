# Free-J graph assembly from explicit witnesses

`zero_of_witnesses` proves in an arbitrary `IΣ₁` model that the actual
95-operation free-J literal vanishes at a given 12-coordinate valuation if
four elements `τ,χ,i,u` of that model's difference ring satisfy the seven
explicit equations

```
Z = M*τ,            τ² = N₀,
D = U*χ,            χ² = 1+(3+4a+a²)c²,
Q = d*i²,           n = i+u,
(1-Q)*(z+u)² + Q*z² - 1 = 0.
```

The letters stand for the *actual graph expressions at that same valuation*,
not independent ports: `M=q³(q−1)` with `q=1+qm`, and `Q,d,z,n` are the
ordinary-tail expressions selected by `parts`. In Lean, `core.n` is the first
carrier's `N₀`, whereas `parts.n` is the coordinate `n`; similarly `core.d`
is the main carrier's `D`, whereas `parts.d` is the tail coefficient `d`.
The proof composes the checked first/main witness bridge, the checked
ordinary-tail bridge and the reverse literal factor bridge.

This is a **conditional** construction interface. It assumes the valuation and
all seven witness equations; it does not yet construct those witnesses from a
halt, establish that the twelve graph coordinates are positive, identify the
ports with a displayed fixed equation, or prove existence of an iPRA
syntactic proof.

The bounded single-author attempt 01 exited 0 in 3.002 seconds without warning
or `sorryAx`. Source SHA-256 was
`3415e46811c5c073df763c6492ada111ce4473d5669d3b960c985a490c52c924`;
object `/tmp/free-j-witness-assembly-author-r44kkvp7/FreeJWitnessAssembly.olean`
had SHA-256
`49a11022dddd0ee1eb7069ba014fa50bd4f01b5369202fd1c0cf9f21ef3f89c5`.
The runner guarded the direct imported object, named transitive bridge
objects and companions, and all 167 files of the two selected live providers;
their 70 overlapping paths matched byte-for-byte. The guard records and Lean
command are in `observations/attempt01/terminal.json`. This is not a fresh
independent replay, a full audit of provider ancestry, or a package-transitive
and dynamic dependency audit. Lean's axiom report lists `propext`,
`Classical.choice` and `Quot.sound` as metatheoretic dependencies.
