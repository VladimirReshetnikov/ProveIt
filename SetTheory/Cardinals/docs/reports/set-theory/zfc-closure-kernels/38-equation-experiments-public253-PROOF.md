# A guarded three-step shortcut in the public 253-state ZFC machine

## Result and scope

The supplied machine `zfc253_shortcut.tm` has **253 working states**, two tape
symbols, a bi-infinite tape initially filled with zero, initial state 0, and a
separate terminal state 253. It changes exactly one transition of the public
253-state machine. The change preserves its complete blank-tape halting
behavior and shortens each use of one guarded three-step path to one step.
The exact published bootstrap endpoint is reached after 312,895 steps instead
of 312,975. All 253 working states remain graph-reachable. **This does not
improve the state-count record.**

The positive contribution here is a small explicit invariant certificate and
an elementary whole-tape simulation proof. The certificate checker is ordinary
Python and was run successfully. No new Coq or Lean proof was compiled. The
source machine's existing Coq proof belongs to its authors; this note neither
rebuilds it nor reclaims their reduction as a new result.

## Attribution and exact input

The original machine is the attributed mira-emmy PR20 reduction of
Mira-Cult's ZFC254 construction, building on Jeff's Coq verification and Andrew
James Wade's framework. Its fixed source is:

- Repository: <https://github.com/mira-emmy/busy-beaver>
- Commit: `0d544f2a2e3c18f12278441a74b7879f31cbe856`
- Literal table: <https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm>
- Source documentation: <https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md>
- Proof endpoint: <https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/e2e/E2E253.v>
- Public pull request: <https://github.com/jeff87654/busy-beaver/pull/20>

The bundled `source_zfc253.tm` is byte-for-byte that table, with SHA-256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
The shortcut table's SHA-256 is
`78dcbd5aa7709f349cb9c378f54909e316c27d448537cf2e9dce15811152c2a4`.
The two files differ in row order as text, because the new table is serialized
in numeric state order; after parsing, exactly one transition differs.

The source itself has 506 transition rows. Each working state has both binary
rows; terminal 253 has none. Every transition target is a working state or the
terminal. Both tables have initial state 0, blank symbol 0, and one-cell left
or right moves. The checker validates these conventions, the exact source and
output hashes, and graph reachability of every counted control.

## 1. The concrete edit

Use the compact state labels in the published table. Replace:

```text
60 0 0 L 45
```

by:

```text
60 0 0 R 51
```

The source contains:

| Current state and symbol | Write | Move | Next state |
| --- | ---: | :---: | ---: |
| 60, 0 | 0 | L | 45 |
| 45, 0 | 0 | R | 43 |
| 43, 0 | 0 | R | 51 |

In the old 254-machine labels used internally by the upstream proof, these
states are 92, 107, 121, and 144. Thus the edit is old92/read0 := 0 R144.

Let the head be at integer position h, let its symbol be 0, and suppose the
symbol at h-1 is also 0. The three old transitions visit head positions
h-1, h, and h+1. Every written symbol is the zero already present. They end in
state 51 at h+1, with the entire tape unchanged. The new transition has that
same outcome in one step. The new transition does not touch h-1. Therefore
the comparison preserves every tape cell, including all cells outside any
chosen finite window.

The hypothesis about h-1 is essential: if it were 1, state45 would take its
other row. It must be proved for every relevant reachable configuration, not
inferred from a long but finite simulation. The finite invariant below proves
exactly that hypothesis.

## 2. The radius-two invariant

At a configuration with head h, encode the five cells h-2 through h+2 by

\[
p=\sum_{i=0}^4 T(h+i-2)2^i\quad(0\le p<32).
\]

For each state q, the certificate gives a 32-bit integer mask I(q). Its bit p
is 1 exactly when the window p is admitted in that state. The file
`invariant_radius2.json` contains all 254 masks, including the terminal mask.
There are 3,530 admitted pairs (q,p). The checker does not trust how the masks
were generated. It verifies the following two properties directly.

**Initial inclusion.** Bit 0 of I(0) is set. The blank initial tape therefore
has an admitted window.

**Transition closure.** Suppose p is admitted at a working state q. Let
b=(p>>2)&1 and let the literal source row be (write w, move d, target q').
Overwrite the central bit to obtain

\[
u=(p\mathbin{\&}\neg 4)\mathbin{|}(4w).
\]

If d is right, the next window is one of

\[
u\!\gg\!1,\qquad (u\!\gg\!1)\mathbin{|}16.
\]

If d is left, it is one of

\[
(2u)\mathbin{\&}31,\qquad ((2u)\mathbin{\&}31)\mathbin{|}1.
\]

The checker requires **both** successor patterns to be admitted at q'. The
newly exposed cell can have either symbol, irrespective of what was forgotten
on the opposite side. This is a conservative abstraction of an arbitrary
bi-infinite tape. It does not assume that an unknown exterior cell is zero.
There are 7,044 checked successor obligations; terminal windows have none.

Induction on the number of actual source transitions now proves that every
actual blank-run configuration has an admitted window. The generator's
breadth-first search is merely a way to find such a closed set. It is not the
soundness argument, and no finite simulation cutoff appears in this induction.

For q=60, the only admitted patterns whose central bit is 0 are

\[
8,\ 9,\ 24,\ 25.
\]

Bit 1, representing the cell immediately left of the head, is zero in all
four. Thus **every source configuration reachable from blank that is in state
60 reading 0 has a zero immediately to the left**. The invariant proves a
stronger fact than the macro needs: the bit immediately to the right is 1 in
these four patterns, but the shortcut uses no assumption about that bit.

As an independent local check, the checker tests all eight five-cell windows
with zeros in positions h-1 and h. The remaining three bits are arbitrary.
The old three-step and new one-step outcomes are equal in every case. Direct
inspection of the three literal rows proves that no exterior cell can be read
or changed in these blocks.

## 3. Whole-run halting equivalence

Write M for the published source and M' for the shortcut machine. Both have
the same blank initial configuration. At any M-reachable configuration C:

- If its state and symbol are not (60,0), one M' step equals one M step.
- If they are (60,0), the invariant proves the local guard. One M' step equals
  three M steps, with equality of control, head, and the complete tape.

Neither of the two intermediate states of the latter block is terminal. Both
cases make strictly positive progress in M and M'.

Inductively, after n steps of M', its full configuration equals the full
configuration of M after t_n steps, where t_0=0 and each increment
t_(n+1)-t_n is either 1 or 3. Hence n <= t_n <= 3n, and every matched source
configuration remains reachable from blank, so the invariant continues to
apply. No assumptions about consistency or about eventual nonhalting are used.

If M' halts, its matched configuration in M is the same terminal
configuration, so M halts. If M' runs forever, concatenating the matching
positive source blocks gives an infinite M run. Conversely, M cannot halt
while M' runs forever, since the strictly increasing sequence t_n would pass
the source's finite halting time; a block cannot cross an unobserved terminal
state. A deterministic machine with a total transition at every working
state either halts or continues, so M halts if and only if M' halts. Equally,
M is nonhalting if and only if M' is nonhalting.

This proof is an elementary finite-invariant argument plus induction on
natural numbers. It can be arithmetized in a weak ordinary base theory and in
particular in ZFC. That statement is about the new table-to-table transport;
it does not claim that this bundle contains a kernel-checked internalization
of the source's full Coq consistency-equivalence theorem.

For any corresponding finite prefix, if e shortcut events occur then
t_n=n+2e. If the machines halt, their respective running times satisfy
n <= t <= 3n and t=n+2e. The count reduction goal concerns working states,
however, and this edit saves none.

## 4. Exact bootstrap comparison

The source's pinned `Boot253.v` proves its exact 312,975-step bootstrap. In
compact labels, the endpoint has state33 and absolute head -17. The complete
tape consists of a marker at -18, forty zeros from -17 through 22, a header at
23, and register blocks of the form 0 1^(v+1) beginning at 24. The nine primary
physical values are

```text
[0, 2, 0, 0, 0, 0, 5, 0, 0]
```

They are followed by all 158 spare blocks. Spare indices 2 and 8 have value 1;
every other spare block has value 0. Every unlisted cell on the bi-infinite
tape is zero. The total number of one-cells is 178.

The full list of 178 integer positions is in `bootstrap_endpoint.json`, not
just a finite tape prefix or a register summary. Its configuration digest is

```text
5f59972252d34cd6a0e4660a65e5ae7409381d00d2a0182e11830224ea77aa5b
```

The digest serializes the object with keys `state`, `head`, `one_cells` as
ASCII JSON with sorted keys and separators `(',', ':')`. The checker also
reconstructs the complete endpoint directly from the stated block shape, so
it does not accept a digest in place of checking the tape.

Literal independent simulations give:

| Table | Binary steps | Uses of state60/read0 | Final state | Final head | One-cells |
| --- | ---: | ---: | ---: | ---: | ---: |
| Published253 | 312,975 | 40 | 33 | -17 | 178 |
| Shortcut253 | 312,895 | 40 | 33 | -17 | 178 |

The endpoints agree cell-for-cell, including all spare blocks and the zero
exterior. The 80-step saving equals 2 times the 40 shortcut uses. These finite
simulations validate the engineering endpoint. The invariant and the argument
in Section 3 establish the unbounded halting equivalence.

## 5. Reproduction and trust boundary

Run with Python 3.10 or later and no third-party packages:

```sh
python check_certificate.py
```

Regenerate the candidate table and certificates from the pinned original:

```sh
python regenerate.py
python check_certificate.py
```

The successful recorded run reports 3,530 invariant pairs, 7,044 closure
obligations, eight independent local macro cases, exact table hashes, and
complete bootstrap equality. The checker uses explicit exception-raising
requirements; `python -O` does not remove them.

The trust boundary consists of the printed mathematical argument, the literal
transition-table and mask data, and the small ordinary Python checker used
to check the finite arithmetic. The generator is untrusted; the checker
validates its output. This bundle supplies neither a machine with fewer than
253 working states nor a new proof-assistant verification of the full
consistency endpoint.
