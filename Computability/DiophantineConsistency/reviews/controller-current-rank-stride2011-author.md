# Derived rank stride and current packing adapter: author verification

This is an author receipt, not an independent review. All four complete
new sources were read before execution. I also read the complete frozen
`CurrentWordRephase2011` and its focused checks, and the exact current
packing interface, before composing the adapter. No accepted source was
edited.

The generic definition is the explicit natural number
`stride d N R = R/d-N`. From `R ≡ d*s [MOD d*N]`, `rank_dvd` derives d|R.
The exact quotient identity d*(R/d)=R follows. With d>0, cancellation of
d on both sides and in the modulus proves R/d≡s modulo N. The growth
premise R>2*d*N proves R/d>2*N, so subtracting N is ordinary subtraction
and leaves a stride greater than N, hence positive when N>0. The module
then proves

```
d*stride d N R = R-d*N,
stride d N R = (R-d*N)/d,
(stride d N R : ZMod N) = (s : ZMod N).
```

No desired divisibility, quotient equation, or stride congruence is an
input. A canonical-value theorem additionally assumes s<N; the primary
cyclic equality does not need that restriction. The existential endpoint
uses this explicit quotient rather than an assumed witness. N=1 and a
zero residue are supported.

The actual wrapper imports the checked finite data and fixes d=94517.
It proves `displacement t = d*t`, followed by
`displacement (derivedStride N R)=R-d*N` and the exact equality of powers
of2. These equalities do not identify arbitrary ordinary multipliers from
their residues; they follow from the derived natural product equation.

`packing_at_derived_stride` retains the particular tile function, dummy
map, source function, carry function, and digit function. The existing
packing and marked-word facts transfer using the derived equality in
ZMod N. Its newly needed scalar quotient may change, as in the accepted
rephasing theorem. R is explicitly supplied with growth/congruence facts;
the wrapper does **not** assert that R equals the rank of that packing.
That binding and final rank calibration remain separate obligations. No
equation-converse or complete controller construction is claimed here.

Frozen sources:

| File | Lines | SHA-256 |
|---|---:|---|
| `ControllerRankStride.lean` |71| `7472a10e6e0deda0e5dd419fcc66fefa5fd83bf695b8607da8889fb88398532f` |
| `ControllerRankStrideChecks.lean` |42| `805ead7d1b7c66eec6cc898f8e1efb50d9fc12514561effb6788fe80b1a85d58` |
| `CurrentRankStride2011.lean` |63| `5f7bbc932de6d984140e518864d275b2f0c655148ecf301d0235ae8e76c790ec` |
| `CurrentRankStride2011Checks.lean` |37| `0ea56ef857067665598d12ad299dafaad6c81b3660de6f5693fc57c263e8b689` |

The generic module imports only `Mathlib.Data.ZMod.Basic` and
`Mathlib.Tactic.Linarith`. The actual module imports that generic module,
`CurrentControllerData2011` (source
`a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae`),
and `CurrentWordRephase2011` (source
`7a1df92104c40f502cc7b62fb1ac04327ce5c842be95172a5483d511a0b99332`).
No current rank-parity module or pending source was imported.

Fresh serial replays used `lake env lean -M6000 -j1 -o` with the matching
source under `Computability/DiophantineConsistency/Lean/DiophantineConsistency`
and output under `.lake/build/lib/lean/DiophantineConsistency`. All four
sources set `Elab.async false`. Every final build exited zero without
warnings. The generic main initially reported an unused positive-d binder
in an arithmetic helper; only its binder name was changed before the
clean final replay. No theorem premise or conclusion changed.

| Fresh object | Time / peak RSS KiB | SHA-256 |
|---|---:|---|
| Generic main |2.62s /1,830,780| `f8aecd41fe5cb78157ede987e79ba534e3225b3a22cf41f6bfccbbbe0ac3125a` |
| Generic checks |2.78s /1,811,480| `bdd95b1182210ba83cd083e0376d0f238e6d764831c3d8feabcd280912678dbb` |
| Actual main |3.46s /3,337,248| `6a9b2eab88da2e0998d15dc30f0ec0ea38fb01c8c67c8cac369d3cee9fbac817` |
| Actual checks |3.57s /3,329,004| `6cf111c5ab4dbcf1c7a74c60fa3d07fe1615f480986805bcaeb788079329c5ed` |

All15 axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`, or subsets. The checks cover a derived stride7 with residue1,
N=1, noncanonical supplied stride7, failure of divisibility without the
rank congruence, zero stride at R=d*N, the actual94517 multiplier, and
the particular-packing adapter. No `sorry`, new axiom, `native_decide`, or
incoming execution was used. Logs are under `/tmp/` with prefixes
`controller-rank-stride-` and `current-rank-stride-`; the final generic
main log is `controller-rank-stride-main-final.log`. No Git operation or
central-document edit was performed.
