# Compact first-port specialization

`FreeJCompactBeta.compact_beta_facts` proves in every model of `IΣ₁` that
for the natural numeral β = 2^590069−1, its model interpretation satisfies
β ≥ 46 and β = 2^590069−1 using the model's internal exponential. The bound
is proved symbolically without expanding the enormous numeral.

`FreeJCompactBeta.compact_graph_alignment` combines these facts with the
independently audited graph alignment. Under the actual 95-row free-J
internal-zero, positive-coordinate and port-bound hypotheses, and the
**explicit natural equality** `p₀ = 2^590069−1`, it constructs model
naturals N,w satisfying

```
N > 0,  q = 2^(590069N),  590069N ≤ R,
w = 2^(R−590069N),  v₅ = q w,
q = 1 + v₀p₀,
R = ((q−1)(q−v₁)+v₂)(q²−1)+(p₂+q p₃)v₀.
```

The powers are internal to the model. The theorem does **not** bind the
actual compact44 payload or literal port to the displayed natural equality;
it assumes that equality. It does not calibrate the checker, prove
existence of an iPRA proof, or establish the final consistency equivalence.
This is a conditional model-level result in classical Lean metatheory.

## Evidence

Exploratory attempt 01 exited 1 with `sorryAx`; attempt 02 exited 0 with a
large-exponent warning. Their exact sources and logs are in `observations/`.
After replacing that computation with a symbolic bound, session 12787
[exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt03.log).
The [paired replay](replay.py) pins the independently audited alignment
parent, matched seed objects and inherited chains, then compiles this source
over fresh author and peer overlays and checks direct imports. It does not
rebuild inherited chains. The graph parent's manifest-at-read qualification
and Foundation outer-wrapper and package-transitive/dynamic ancestry
limitations remain; resource sampling is not a continuous
whole-process-tree hard quota.

Outer session 95765 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `81656fc5e691c76f51260c6475ae9b14fc2aa15fcc6a4550dc13ede5694ad823`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-compact-beta-new
```
