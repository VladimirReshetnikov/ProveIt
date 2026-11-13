# Exact even-half-index residue modulo a divisor

`Trace74ExactAuxIndexResidue.even_quotient_mod_divisor` proves in every
`IΣ₁` model that, for `I≥2`, `c>0`, and `c|I`,

```text
oddQuotient (2t) (I−2) mod c = (4t+1) mod c.
```

The represented functions and `t` are internal model quantities. This
refines the existing signed-disjunction theorem to the positive branch at
even half-indices. Its paired induction uses the same checked recurrence
transport as that theorem and the preceding
[exact main-ordinate residue](../trace74-exact-aux-pell-residue/README.md).
The norm and graph witness are not supplied here; this lemma alone is not
an iPRA endpoint or a formal counterexample construction.

The author check used Lean 4.32.0, `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74ExactAuxIndexResidue.olean`. Actual session 86632 exited 0
without warnings and reported only `propext`, `Classical.choice`,
`Quot.sound`.

Source SHA-256:
`de2d7e1a00a62bc278d47005a13da8f96526f79e2246e0b26ebecf22a1c87240`.
Output object SHA-256:
`cc2366efe799a1f9031f5f45817ec790a480211ad8f0c13c0f8ba2efcf80948e`.
Direct imported `Trace74ExactAuxPellResidue.olean` SHA-256:
`554cc19fb4b5e426ad7ca0ddf104032fdd8880b29733f139ab8a8e9efcf79880`.
The captured providers, full transitive/package/dynamic ancestry and
search-path resolution have not been independently authenticated. This
is not a coherent current-source rebuild or an independent replay.
