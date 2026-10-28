# Independent current C222 finite circuit review

26 October 2026. PASS, with no requested source changes. Root authored
the reviewed 134-line main and 36-line checks. Controller-certificate read
both complete frozen sources, both complete author drivers, the author
receipt, and the relevant actual append/J/word/leaf interfaces before a
fresh private replay. The reviewer authored the accepted Block and Leaf
dependencies and the separate Rule packet; this is an independent review
of root's new circuit representation, not of those prerequisite authorships.

The external finite `Circuit` syntax has four inputs and a fixed five-slot
Σ1 graph in order `(out,a,b,c,u)`. Its graph is defined before any ambient
model is selected. Each binary node existentially binds the two actual
child values with the same four input slots. Structural induction proves
exact interpretation using the accepted arithmetic, Cantor, implication,
append and J graphs. This does not posit an internal circuit evaluator or
invoke induction on unrepresented internal codes. Truncated subtraction,
zero-J, and all internal inputs are preserved.

The physical NIP/DROP words have no operand fields. MP retains tag2, and
AX has the literal API order `(c,x,y)` but physical payload order `(y,x)`.
All fixed NIP, discard, terminator and leaf expressions agree with their
accepted runtime words. In particular the focused row8 client still
requires `u≤a`; it does not assert unrestricted row8. No hidden source
axiom, semantic truth assumption or desired execution contract was found.

Source pins:

- Main `24427d6d6a643245630a7ea18bc94141ac923a0fffe6a7e3ae86f5309002f75d`.
- Checks `3e1f006d0291413d3157ef1e8f48b50bc5a589ca5cec6181b5fbdb893a572214`.
- Author replay `a3ae9fa755656301a64322137e3be00c52780412a065ac34dd6e0f343a7aaa06`.

Independent fresh main/check replay passed in 7.195s/1.984s. Main diagnostics
were empty; all nine check reports contain only `propext`, `Classical.choice`
and `Quot.sound`. Peak RSS was 1,850,624/1,814,192 KiB. Both objects are
byte-identical to the author's, respectively
`d83c48d8a1f602df710c7901ae95a4f213dcbc35ebecfdfce51fa7d8e2e03649`
and `aabd3d154b7361fd98d62e3af4a54ef937b32ee3bfa92feb236c7350f03129d4`.

The private overlay is `/tmp/command-circuitperm222-controller-peer-hxn867qf/lib`.
It reuses 124 authenticated custom modules, including 95 Foundation modules,
409 artifacts and 38 explicit external import boundaries. All import lists
were rechecked. The author's 1,130 inherited observations plus explicit
peer/source/artifact/manifest observations total 1,722 checks before and
after execution; this count includes repeated observations. The target
stems were excluded from the cache, and both fresh outputs were regular
nonsymlink files. `LEAN_PATH` uses only this overlay, the explicit package
providers and pinned Lean4.32; it excludes the shared project object cache.
Each invocation used `-M6000 -j1 -DElab.async=false` and checked the 512MiB
reserve. No dependency/Foundation build, source edit or shared-object
mutation occurred. There were no failed peer compiler attempts; the
author's three preserved namespace failures remain in the original packet.

[Independent replay](arithmetic-command-circuitperm222-peer-replay.json)
SHA `cc9eb01429ec98bb92f56b84f3372e17d9d9fabf10b92d4f23ea7e6fcd4bcd70`;
[nine-file evidence manifest](arithmetic-command-circuitperm222-peer-replay/FILES.json)
SHA `95e552cc40b647d9f1c087a7b2f25f1a91a387ee1bddf3824ba30db3a8437aa0`.
These preserve the complete peer driver, inputs, commands, snapshots,
logs, timings and result; objects are pinned rather than copied.

Separately, source-only inspection of the complete generic
`DominatedImplication` derivation supports the proposed next uniform-row
construction. Its circuit existential must precede every model/input
quantifier; pointwise internal-word existence is insufficient. Syntactic
`Below` growth uses actual `tagged_components 0`, and generic major-first
MP must be connected to the actual minor-first `mp_contract` with the
hypotheses correctly ordered. That next construction was not compiled or
proved in this review. No full compiler, seed calibration, or HA endpoint
is claimed by this finite-circuit checkpoint.
