# Native adaptive rank-window author receipt

The two new leaves passed a fresh private Lean replay. This is an author
receipt, not an independent review. The final 225-line main, 55-line focused
checks and complete driver were read before the final execution and reread
before this freeze. Existing accepted sources and shared objects were not
modified.

## Mathematical scope

`NativeAdaptiveRankWindow.adaptive_early_bounds` takes the literal `firstA0`
and `mainA1` zero equations, the displayed positive integer variables, the
actual transport/target definitions, `NativePellBootstrap.PortBox`, and
`15 ≤ ports 0`. Its high-mask argument is the already once-shifted port.
It derives `3*q < R`, `R+1 < q^4`, both first/main Pell classifications,
first index `n ≥ 25`, `n < p`, main index `p ≥ 6`, a positive integral main
ordinate, `A*(A^2-1)^2 < c`, `2*p < c`, and `2*R < c`.

The proof first gets positive transport and `q^3 ∣ Y` from A0. The target
window then supplies positivity needed by A1; A1 supplies `q^4 ∣ k-R-1`
and the positive main classification. The first congruence uses
`Pell.yn_modEq_a_sub_one` and signed integer divisibility. It does not assume
a nonnegative quotient for `k-R-1`. The stronger base separation required by
`main_index_gt_first` is proved explicitly. Both classifications and all
index bounds are conclusions, not supplied premises.

Other public helpers are `target_window`, `first_index_residue_of_dvd`,
`first_index_lower_of_dvd`, and `base_separation`. The focused client applies
the complete literal A0/A1 theorem to obtain `2*R < k*Y+eta`; numerical
checks exercise the signed divisibility and base separation helpers.

This packet does not restore a source certificate, prove the strong norms,
identify the main index with the target, recover a power, prove a canonical
converse, or establish a new equation/ConZFC or internal-HA endpoint. It has
no source, rank, oddness, or already-classified-index premise.

## Frozen files

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/NativeAdaptiveRankWindow.lean` | `f536f9324408a9660967e62baf10f01d85ed45ef7e4619e1c9f32710c6bd9b52` |
| `Lean/DiophantineConsistency/NativeAdaptiveRankWindowChecks.lean` | `7d9934983310cf105e16d066487c38bb51cdc86d33e65984353deb1881f8515a` |
| `reviews/native-adaptive-rank-window-replay.json` | `e0a654c766eb882ce6f294c1a916dd304436c3e13d8f3f05ee05125bec63d3dd` |
| `/tmp/native-adaptive-window-driver.py` | `10785dd5b28639a902326cbd6f820643893e28532ee1d820b2379bc4b74e7fae` |
| `research/adaptive-rank-window2011-proposal.md` | `204fb46b56c472f3a2e859bd5a4f795836a94599e360bb90302c433ab90c546f` |
| `research/adaptive-rank-window2011-cache-audit.json` | `6419ec8955372535c1855c00c926762472d714fc607002acd11a1c783d22facd` |

The main imports only `NativeAdaptiveMainBootstrap`; the checks import only
the new main. The exact private closure reuses 28 authenticated custom
source/object pairs, 22 actual external boundary names including implicit
`Init`, and 66 external object companions. The cache audit pins the accepted
A0 and FactorThree dependencies and root's accepted A1 provider
`/tmp/native-adaptive-main-root-9pp4_mhm/ROOT.json`, SHA
`65988589bee87bebfc0ccae84b3eafa6277d3bc95c650ddbe4d99500cca55824`.
All 151 direct input pins and actual custom import headers were checked.
The existing dependency authentication is reused; this is not a new full
closure or external-package rebuild.

## Final execution

Private directory: `/tmp/native-adaptive-window-o0wgi9j6`.
Final `inputs.json` SHA:
`9e5715300d6713bb8cbb9ed966f2a55260c1369bd63f167e194c66b291c8bf00`.
Final `state.json` SHA:
`001e86fa696632dc69c2778a3c93ba687989b30c0541c5f1938650227ca4241a`.

Both commands used the pinned Lean 4.32.0 binary with
`-M6000 -j1 -DElab.async=false`, one process at a time. `LEAN_PATH` contained
the private overlay and the authenticated external roots, without the
shared project build path. Reused object links were read-only inputs; the
two output paths were initially absent and became regular, nonsymlink
files. No dependency or Foundation build was run. The 512 MiB reserve was
checked before and after execution; packaging found 2,264,231,936 free bytes.

| Leaf | Exit | Seconds | Peak RSS KiB | Object SHA-256 |
| --- | --- | --- | --- | --- |
| Main | 0 | 10.011 | 3,280,572 | `ed6546c60575c4bbd9487e96a9215b0be19247d23a1e51ccd6950675ea0a8942` |
| Checks | 0 | 2.856 | 3,206,980 | `2183c0184a75f58bcb88943b149af046d68721e8dda9c422f5df27e91beabc30` |

The final main log is empty. The checks log contains exactly five axiom
reports, each limited to `propext`, `Classical.choice`, and `Quot.sound`,
with no warnings or errors. Final source, dependency, log, snapshot and
object hashes were rechecked before packaging.

## Preserved attempts

1. `/tmp/native-adaptive-window-m328j1pn`: main exited 1 after 34.665 s.
   A signed-divisibility conversion needed an explicit negative witness;
   two `rfl` steps followed goals already closed by rewriting; and a late
   broad arithmetic tactic exhausted its default heartbeat budget.
   The repair used the explicit witness, removed the two redundant steps,
   and restricted arithmetic tactics to their relevant hypotheses. No
   public theorem statement or resource cap changed. Checks were not run.
2. `/tmp/native-adaptive-window-fqv0qq5l`: both leaves passed, in 10.894 s
   and 2.902 s, with five standard axiom reports. Two checks-only linter
   warnings concerned inline Pell-base bound proofs. A named private
   `base17` proof removed them; mathematical statements were unchanged.
3. `/tmp/native-adaptive-window-o0wgi9j6`: the final clean pair above.

The durable replay JSON embeds the full driver, all three input/state
records, every executed source snapshot, log and timing file, plus the
frozen proposal and cache audit. Binary objects remain private and are
identified by their exact hashes. Every failed or warning-bearing attempt
is retained, rather than replaced by the final clean result.
