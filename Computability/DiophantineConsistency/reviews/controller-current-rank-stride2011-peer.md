# Independent review: rank-derived stride and actual packing adapter

**PASS, with no source correction requested.** The controller-certificate agent independently read all four frozen sources and the complete author receipt, then freshly compiled all four in an isolated object overlay. The reviewer did not author these four modules; complemented47_review did. The reviewer authored several reused local word, clause, top-bound and scalar-witness dependencies, so this is an independent review of the new arithmetic and composition, not an independent reimplementation of every prerequisite.

## Mathematical review

The generic module defines the actual natural number `R/d-N`. The congruence `R ≡ d*s [MOD d*N]` implies `d ∣ R`, and hence `d*(R/d)=R`. Its cancellation theorem cancels `d` in both operands **and** the modulus under `d>0`; no coprimality condition is needed or silently assumed. The growth bound `2*(d*N)<R` yields `2*N<R/d`. Thus subtraction by `N` does not truncate in the cyclic-residue proof, and the resulting stride exceeds `N`. Positivity additionally uses `N>0`.

The natural equation `d*(R/d-N)=R-d*N` is valid even without the growth condition, by distributivity of natural truncated subtraction. With `d>0` it also gives the exact printed quotient `(R-d*N)/d`. The principal cyclic equality does not require `s<N`; that extra condition appears only in the theorem identifying the canonical `.val`. The small checks include `N=1`, a noncanonical supplied stride, zero stride when growth fails, and failure of divisibility when the congruence is removed.

The actual module binds `d=47*2011=94517` and `displacement t=47*(2011*t)`, so its claimed exponent and power equalities are ordinary natural equalities. It does not equate ordinary powers merely because their exponents have equal cyclic residues.

I also read the complete `CurrentWordRephase2011`, its checks, and the full `CurrentNativePacking2011` interface. The actual adapter invokes rephasing with the correct direction of the derived residue equality. It preserves the particular assignment, dummy function, complete source function, carries and normalized digits. Canonical shifted-marker equality and the equality of physical binary rotations justify reuse of those objects, including wraps. The ordinary temporal multiplier may change, and the positive transport quotient is recomputed rather than asserted equal to its former value. The low/high masks, repunit window and scalar bounds refer to the same retained words.

The scope restriction in the source is accurate and necessary: **`R` remains an explicit natural argument with growth and congruence hypotheses. This packet does not establish that `R` is the rank of the supplied packing.** It assumes a particular packing and marked word for its adapter, rather than proving either from a halt. Actual rank calibration, controller target selection, complete Pell witnesses and a polynomial converse are not conclusions here. No hidden rank identity or final equivalence premise was found.

## Exact frozen sources

Paths are under `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines / bytes | SHA-256 |
|---|---:|---|
| `ControllerRankStride.lean` | 71 / 3,010 | `7472a10e6e0deda0e5dd419fcc66fefa5fd83bf695b8607da8889fb88398532f` |
| `ControllerRankStrideChecks.lean` | 42 / 1,605 | `805ead7d1b7c66eec6cc898f8e1efb50d9fc12514561effb6788fe80b1a85d58` |
| `CurrentRankStride2011.lean` | 63 / 3,007 | `5f7bbc932de6d984140e518864d275b2f0c655148ecf301d0235ae8e76c790ec` |
| `CurrentRankStride2011Checks.lean` | 37 / 1,682 | `0ea56ef857067665598d12ad299dafaad6c81b3660de6f5693fc57c263e8b689` |

The author receipt `controller-current-rank-stride2011-author.md` has SHA-256 `e1afe1b3594f13b07a078a48f22d7d7e4d8bea066199f3d38b97c87aedce7928`. The exact reused actual direct sources are `CurrentControllerData2011` (`a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae`) and `CurrentWordRephase2011` (`7a1df92104c40f502cc7b62fb1ac04327ce5c842be95172a5483d511a0b99332`). Its packing dependency is `CurrentNativePacking2011` (`df17b8a5c2913b2ffec6d4b6fbd3fe5127aa45e76273ed88734f30da548fa92e`). I checked the invoked cancellation/subtraction facts in pinned local mathlib and the actual definitions of `d` and `displacement`.

## Independent capped replay

Fresh outputs were written only under `/tmp/controller-current-rank-stride-controller-peer/lib/DiophantineConsistency/`. The four reviewed stems were excluded from reused-object symlinks, and the overlay path was prepended to `LEAN_PATH` **after** `lake env`. The actual main therefore imported the fresh generic object, and each checks file imported its fresh main. All other prerequisite objects were reused; no fresh compilation of the entire dependency closure is claimed. No existing object or source was overwritten.

Commands used Lean `v4.32.0`, `-M6000 -j1`, and the sources' `Elab.async false`. An initial overlay missing the symlinks for other `DiophantineConsistency` imports caused an import-resolution rejection before the actual main proof could run; completing the overlay fixed that environment issue without source edits or cap changes.

| Final replay | Wall seconds | Peak RSS KiB | Exit | Fresh object SHA-256 |
|---|---:|---:|---:|---|
| Generic main | 2.88 | 1,830,876 | 0 | `f8aecd41fe5cb78157ede987e79ba534e3225b3a22cf41f6bfccbbbe0ac3125a` |
| Generic checks | 2.29 | 1,812,720 | 0 | `bdd95b1182210ba83cd083e0376d0f238e6d764831c3d8feabcd280912678dbb` |
| Actual main | 3.47 | 3,337,644 | 0 | `6a9b2eab88da2e0998d15dc30f0ec0ea38fb01c8c67c8cac369d3cee9fbac817` |
| Actual checks | 3.42 | 3,329,752 | 0 | `6cf111c5ab4dbcf1c7a74c60fa3d07fe1615f480986805bcaeb788079329c5ed` |

All four objects are byte-identical to the author objects. Both main logs are clean. All fifteen requested axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`, or subsets; the final replays have no warnings or errors. Source search found no `sorry`, `admit`, `native_decide`, `unsafe`, or declared axiom. Sixteen pinned source/object/receipt/toolchain inputs were unchanged after replay.

Local evidence in the overlay directory:

| File | SHA-256 |
|---|---|
| `inputs.json` | `7cf225ee7e08dfb613389cae6308aeba9587f27d692120e75c90697bdc020379` |
| `result.json` | `2dbf690ac1efe0e3a3734f69fb5f1f80f93ec6d9e180c8c898822921457e315f` |
| `generic-main.log` | `e0ef828d857b7bcd49e80b3c6f62046fc5d7bb9f1c6b28541efb33c8f2f07b16` |
| `generic-checks.log` | `85688c05ad4a36d864fcaf752d0a43357f1eae9328e73ce1a51073cadeaff772` |
| `actual-main.log` | `c981dbe1fe1e2b592aa30926e8d0fd735fdd294fe2cc22ffe1d36fc37c1c20b2` |
| `actual-checks.log` | `5ceae5432720e3c95a3fcc22c4e1de5f7cbb0b11aba77844bbe6e26673c5bbe4` |

These `/tmp` files are local replay evidence, not durable proof prerequisites. Only this new review receipt was added to the repository; no frozen source, central document or git state was edited.
