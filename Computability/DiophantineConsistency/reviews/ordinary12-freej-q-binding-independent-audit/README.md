# Independent audit of the free-J graph q binding

The independent artifact audit actually exited 0; receipt SHA-256 is
`9c4d90de367378a47461bb979a37fe86d32972238d826249dba58fccd5baa90f`.
A fresh bounded Lean replay in separate temporary paths actually exited 0 in
session 1014. Its full replay and nested rank receipts are retained here, with
hashes and observed exits in `terminal-observation.json`. The original saved
replay is pinned. Fresh and original q-binding source, object and successful
compiler log match by hash; the five named reports and direct dependencies
were independently checked. Optimized Python is deliberately rejected.

The previously independently checked 95-row graph has `J` in variable slot 0,
`beta` in port slot 0, `qm=J*beta` and `q=1+qm`. The checked source quantifies
an arbitrary integer port tuple `p` and model valuation `v`, and explicitly
assumes `0 ≤ p 0`. It proves the `qm` signed pair equivalent to the natural
pair for `v 0 * (p 0).toNat`; it proves the q pair is exactly the natural pair
for `1 + v 0 * (p 0).toNat`, hence positive. `graphQ` is its first component.
A small independent arithmetic check covers nonnegative beta including zero;
a negative-beta example demonstrates why the premise cannot simply be erased.

The graph-cancellation theorem still explicitly assumes the **model-level**
equality `((p 0).toNat : V)=Exp.exp (590069:V)−1`, the two divisibilities
`q³ ∣ Y` and `q⁵ ∣ (3+4Y(X+1))t`, and the later premise `q ∣ 3·Exp.exp R`.
It then applies the independently reviewed conditional rank adapter to derive
`q⁴ ∣ t` and `q ∣ Exp.exp R`. `Y,X,t,R` remain separately quantified and are
not identified with the graph valuation. Five source/theorem mutations were
rejected. No derivation of those hypotheses or compact44 checker calibration
is supplied by this q binding.

The audit pins the separate manuscript graph and four-port evidence: its beta
payload has 590069 bits and raw SHA-256 `0664a868…`. That finite byte binding
does not establish the displayed model-port equality. It also rechecks the
62-module historical source closure, parent source/object/log hashes, 62
linked objects and 558 absent companions. Both rank and q direct imports are
re-queried; the rank object copied into the overlay is a distinct inode with
the same hash as the separately audited adapter. The nested free-J object,
provider receipt and Lean binary are pinned.

This is bounded single-author historical model evidence, not a matched full
project replay or complete dynamic/package-transitive ancestry audit. It does
not derive rank divisibility, norm recovery, checker calibration, consistency
equivalence or an internal iPRA theorem. Between-observation mutations and
the Foundation provider's unobserved wrapper exit remain outside its guards.
