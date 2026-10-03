# Independent review of whole-period Grill padding

**PASS.** The [padding theorem](grill_tag_padding_period.md) is an exact deterministic coupling. It both reduces existential padding to finitely many residue classes and justifies a separately emitted one-multiplication saving in the native compiler. It does not establish a universal input decoder.

Root read the complete proof and standalone checker. An initial word of length L cannot disappear before all L of its initial symbols have been consumed. Appended output always follows the remaining initial suffix. At that time the two initial queues `w` and `w0^k` have become `G(w)` and `0^kG(w)`. Consuming the k zeros creates no output. For k divisible by the program period, the second run reaches exactly the first run's queue **and phase**, with a k-step delay. Empty and all-zero inputs have the claimed first-halt times as well. This proves halting equivalence and the exact first-halt shift without assuming termination or inferring nontermination from a cutoff.

Every admissible bit length has one canonical representative modulo the program period m. Therefore at most m canonical padded inputs suffice semantically. The computed bit length in this statement remains a mathematical description, not an uncharged circuit operation. The explicit period-two example `(2,0)`, input1, halts from `10` after9 steps but enters an exact period12 cycle from `100`. This rules out replacing the residue union by an arbitrary single padding choice.

For the proposed weak cone `P0>x`, adding 2m zero bits multiplies P0 by `4^m`, putting it above `3x` while preserving halting. Strong-cone inputs already belong to the weak cone. This proves equality only after existentially quantifying the padded run. The native sentinel argument still has `0<x<P0`, and on positive coordinates the modified height has `D>=5` and exceeds every required endpoint and phase value. Thus a separately checked source child may remove the multiplication by3. Its reverse language implication must rebuild the accepted run and native witnesses; it is not equality of positive witness sets or of full polynomial values.

The [independent checker](review_grill_padding_period.py) pins author source SHA256 `299acc95d66b60fb7fe2b3e3a85ffd3ec7c77f8c53ce2f11d1b59d9f7d59ba48`, but does not execute the author's simulator. It uses a separate deque implementation and checks:

- 25,704 exact synchronization identities over all exponent-0/1/2 programs of periods1–3, all nonempty binary words of lengths1–6, all initial phases, and one or two periods of padding.
- 23,114 canonical residue factorizations for both cones and 7,112 checks of the uniform weak-to-strong lift.
- Seven explicit semantic fixtures: three certified first halts and four nonempty repeated configurations proving nonhalting, including all three canonical padding residues for program `(0,1,1)`, input2.

The [receipt](review_grill_padding_period.json) records the full fixture outcomes. Its `width` fixture field is the bit length ell; the numerical width is `P0=2^ell`. Root independently replayed the author's broader suite and reproduced its saved receipt byte for byte. That suite explicitly leaves 431 bounded runs unresolved. Neither suite treats a timeout as a nonhalting certificate. The general theorem follows from the coupling above, rather than finite enumeration.

Both checkers use standard Python only:

```sh
python grill_tag_padding_period.py --expect grill_tag_padding_period.json
python review_grill_padding_period.py --expect review_grill_padding_period.json
```
