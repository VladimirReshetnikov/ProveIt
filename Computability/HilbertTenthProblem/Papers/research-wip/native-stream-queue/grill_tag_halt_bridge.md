# Corrected Grill block compilation preserves the halt protocol

This closes one concrete gap in the Grill route: the corrected block compiler converts a well-defined, two-output Genera computation into a Grill queue that empties **if and only if** the source produces its halt symbol. The proof includes the final cleanup, not just the nonhalting E/L/R simulation. It also identifies exact arithmetic ports for a future binary-input block loader.

It does **not** establish an ordinary-input universal Grill recognizer. The current native compiler existentially permits terminal zero padding; the previously proved [encoded-padding obstruction](grill_tag_encoded_padding_obstruction.md) still prevents plugging these encoded integers directly into that relation. No complete fixed universal Genera program, general ordinary-input decoder or improved universal-polynomial count is supplied here.

## 1. Source and precise corrected construction

The primary sources are the creator's [Grill Tag construction](https://esolangs.org/wiki/Grill_Tag), whose current footer identifies [revision 181950](https://esolangs.org/w/index.php?title=Grill_Tag&oldid=181950), and [Genera Tag](https://esolangs.org/wiki/Genera_Tag), footer [revision 182460](https://esolangs.org/w/index.php?title=Genera_Tag&oldid=182460). Both were reopened for this work. They are an informal creator construction, not a peer-reviewed or proof-assistant-checked compiler. The linked Perl compiler was inaccessible; no downloaded program is executed or claimed to have been audited.

The E description's second long grill must still be corrected from `a−2` ones to `a−4`. That four-bit discrepancy is proved and boundedly tested in [the prior source audit](review_grill_encoding_e.md); this packet explicitly uses the corrected version and does not silently certify the erroneous prose. Its independent compiler specializes byte-for-byte as a program tuple to the previously reviewed nonhalting two-symbol constructor, whose source is authenticated before use.

Fix an alphabet with N≥2 symbols, numbered 0,…,N−1, one of which is the halt symbol H. Every other symbol y has width w_y∈{0,1} and two ordered output symbols at each source phase p∈{0,1}. Put

    a=28(N+1),     m=14a,     g(r)=0(10)^r.

A Grill macrostep processes one run: a zero is removed without output; a one is removed and appends g(n_p); then the run phase advances modulo m. All times below count these **run/macro steps**, not individual `11` commands or bit complexity.

For nonhalting y, let e_y=7a(1−w_y). For H put e_H=3a/2. The literal block definitions are

    E_y = 0^(14y+7) g(a−3) g(7) g(a−4) 0^(3a−14y−10+e_y),
    L_y = 0^(a−3) g(14y+7) g(3) g(3a−14y−10) (10)^e_y,
    R_y = 0 g(14y+7) g(3) g(3a−14y−10+e_y) 0^(a−4).

For y=H, `E_H` in this display means a **cleanup intermediate** E_H*, not a permitted source input: it is the ordinary width-one E base followed by 3a/2 zeros. Thus

| Block | Nonhalt, width 1 | Nonhalt, width 0 | Halt |
|---|---:|---:|---:|
| E | 7a | 14a | E_H* has 17a/2 |
| L or R | 7a | 21a | 10a |
| Number of ones in E | 2a | 2a | 2a |
| Number of ones in L or R | 3a | 10a | 9a/2 |

All entries are integral because a is divisible by 28.

The [standalone source](grill_tag_halt_bridge.py) writes the literal run table. In each half of length 7a, the R→E positions are `28y+17,19,21`, with values `a−3,7,a−4`; the L→E positions are `28y+a+13,15,17` with those same values. These rows are included for H too. For a nonhalt source y producing `(u,v)` at that half's source phase, the seven E→LR positions `14y+2a+3,5,…,15` receive

    14u+7, 3, 3a−14u−10+e_u, 0,
    14v+7, 3, 3a−14v−10+e_v.

All other runs have exponent zero. There is no E-production rule for H. The construction is a finite, explicit table for any supplied finite source table: m=392(N+1) runs, exactly 24N−12 of positive exponent. These are table-size counts, not an arithmetic SLP bound or an instantiated universal table.

## 2. The modular erasure fact

Modulo 7a, every possibly nonzero run position is odd and lies strictly between 0 and 5a/2. The three ranges are disjoint:

    R→E: 17 through a−35,
    L→E: a+13 through 2a−39,
    E→LR: 2a+3 through 5a/2−13.

The exact listed positions inside each range do not collide. This follows from their spacings and a=28(N+1); the ranges also leave the whole interval [3a,11a/2) free of nonzero runs. Adding 3a to any active position therefore lands on a zero run, without wrapping modulo 7a. Adding 3a preserves parity.

In any normal E, L or R block, the ones of its variable-length grills lie at even offsets from a phase in {0,7a}. Only the ones of the small fixed grill lie at the displayed odd active positions. The extra `(10)` repetitions of L, including the halt extension, also place their ones at even offsets. Consequently, at a start phase in `{3a,10a}`, **every one of any E/L/R block selects exponent zero**, and every zero selects no output. Processing the block produces exactly as many zero bits as it originally had ones. The same assertion holds for the E_H* intermediate.

This is a general support argument for every finite table of this shape. The finite support and word checks in the receipt are regression evidence for its implementation, not its proof for arbitrary N.

## 3. Ordinary generations and the halt cleanup

Write `Gen_p(w)` for processing exactly the bits initially in w, collecting appendants as the next word. It is a literal FIFO generation; no appended output is processed early.

At normal phase 7ap, processing E_y for a nonhalt y produces exactly `L_u R_v`, where `(u,v)` is its source production at p. The phase advances by `7a w_y mod14a`. One can read the word identity directly from the seven active outputs: the middle zero is the initial zero of R_v, and extending the third grill is exactly appending the required `(10)` repetitions to L_u. Variable-grill ones supply the leading and trailing zeros of the two blocks. This also works when u or v is H.

At either normal phase, processing L_y or R_y produces E_y, or E_H* when y=H. The three active outputs are `g(a−3),g(7),g(a−4)`, with the required surrounding zeros produced by variable-grill ones. The additional 3a/2 ones in a halt block produce 3a/2 extra zeros, which accounts for the exact E_H* word above.

If the produced source word contains no halt symbol, it has even length: every source symbol produced exactly two symbols. Each ordinary L/R block has length 7a modulo14a, so the whole LR word has length divisible by14a. The LR→E generation therefore preserves its initial normal phase. Together these identities prove the two-generation simulation of an arbitrary nonhalting source generation, with the correct persistent Genera phase.

Now let v have even positive length and contain exactly one H at zero-based index j. Alternate L/R blocks to encode v, starting at any normal phase. During this LR generation:

1. The j blocks before H produce their ordinary E encodings.
2. H produces E_H*. Its length is 10a instead of 7a modulo14a, so it shifts every later block by exactly 3a.
3. Each later block produces only zeros, by the modular erasure fact.

The whole LR word has length 3a modulo14a. Its output is exactly

    E_(v_0) … E_(v_(j−1)) E_H* 0^Z,
    Z = sum_(i>j) [3a+7a(1−w_(v_i))],

and its next start phase is the original phase plus3a. Each preceding E block has length 0 or7a modulo14a, so all its ones, and all the ones of E_H*, are now on zero runs. The appended tail was already zero. Thus the following generation is exactly

    0^(2a(j+1)),

and one more generation empties the queue.

These three generation lengths give an exact remaining first-halt time from the LR boundary:

    L1 = 10a + sum_(i≠j) [7a+14a(1−w_(v_i))],
    L2 = 17a/2 + sum_(i<j) [7a+7a(1−w_(v_i))] + Z,
    L3 = 2a(j+1),
    T_remaining = L1+L2+L3.

Each length is strictly positive. A FIFO queue cannot empty while any part of its initial-generation suffix remains, and its next word is nonempty at the first two generation boundaries. Therefore this is the **first** empty time, not just a time by which it is empty.

For example, with N=2, a=84 and one width-one nonhalt symbol A, let both phase productions be `A→HA`. Its E input has 588 bits. The subsequent lengths are 1428,966,168, and the exact first-empty time is 3150 runs. For `A→AH`, the lengths are 1428,1302,336 and the time is3654. Both initial source phases agree. The `A→HA` cases satisfy the published Genera halt convention because the prefix before H is empty. The `A→AH` cases violate its hypothetical-prefix restriction: the preceding A would produce another H in the next generation. Those latter cases test the stronger one-H cleanup lemma only, not the valid-source simulation theorem. The receipt stores eight whole FIFO trace hashes, including both width choices and both halt positions, using a second implementation that does not call the generation evaluator.

## 4. What has been proved about halting

Start from a nonempty word of nonhalt symbols, at source phase zero (the argument also permits either initial phase). Assume the Genera execution is well-defined under its published halt convention: at its first halting generation there is one H and no forbidden additional halt generated from the prefix in the convention's hypothetical next generation. Before that point all productions have length two, so every source word is nonempty.

The normal identities synchronize the encoded Grill run at every nonhalting E boundary. Such a run cannot empty between those boundaries. If a source generation produces its one H, the cleanup proof gives a finite first-empty time. Conversely, if no source generation ever produces H, every E→LR→E pair stays nonempty forever, and the Grill queue cannot empty. Hence

    the valid Genera computation halts
      iff the Grill run from its exact corrected E word empties.

The cleanup argument actually needs only one H in the produced even word; it does not use the additional prefix restriction. This does not redefine the creator's behavior on undefined Genera inputs. Multiple-halt words and initially halted input conventions are outside the theorem; neither is needed for its stated simulation interface. Because productions have exactly two outputs and the initial word is nonempty, the source's special empty-word nonhalting behavior is not reached and is not mistaken for Grill's empty-queue halt.

This is a new general proof for a **corrected** literal compiler schema, with its previously missing halt bridge now supplied. The prior source audit's finite two-symbol tests alone did not prove it. It still does not furnish a chosen universal Genera table or independently establish the full chain from arbitrary ordinary input to that table.

## 5. Exact input ports, and why a decoder is still unpaid

The E numeral has a simple structure. Let `val` read a word little-endian and put

    gval(r)=2(4^r−1)/3,
    A_a=2^7 [gval(a−3)+2^(2a−5)gval(7)+2^(2a+10)gval(a−4)],
    K=2^(7a), D=2^14.

For every nonhalt symbol y,

    val(E_y)=A_a D^y,
    |E_y|=7a(2−w_y).

The width changes only terminal zeros; the numeral is unchanged. Thus the exact encoded numeral and width of a source word y_0…y_(n−1) are

    X=A_a sum_i D^(y_i) K^(sum_(j<i)(2−w_(y_j))),
    P0=K^(sum_i(2−w_(y_i))).

Every E block has many trailing zeros, so every nonempty encoded word satisfies `0<3X<P0`. The strong and weak native cones themselves pose no issue on this exact encoding.

For a binary input alphabet 0/1 whose two symbols both have width one, a regular recoder could return

    R=sum_(i<n) b_i K^i,  J=sum_(i<n)K^i,  P0=K^n.

Then `X=A_a[J+(D−1)R]` and the native weak-cone slack is `Z0=P0−X`. Conditional on these genuine recoder ports, evaluating X and Z0 takes exactly **two multiplications and two additions/subtractions**: multiply R by D−1, add J, multiply by A_a, subtract from P0. These four gates do not include the recoder, selection of canonical input length, its domain constraints or the full native finalizer. They are an explicit interface formula, not a complete loader or a claimed universal count. The checker verifies it for all255 canonical positive binary words of lengths1–8.

A complete ordinary-input loader must still pay for these ports with the correct bit orientation and length. For canonical binary input, a dyadic port Q=2^n must satisfy `x<Q<=2x`, rather than freely choosing n. It must then force the Grill initial width to **this** P0, not allow arbitrary terminal zeros. The existing native polynomial computes P0 from its own positive width slack; linking or substituting that coordinate requires an actual paid source composition and positivity proof. Finally a fixed source program must be proved to recognize the intended input language on these binary source words.

The obstruction is concrete, not hypothetical. The previously frozen two-symbol nonhalting fixture has exact E input E^k with an infinite encoded run, but the same integer padded by six further zero bits halts. Both widths lie in the native cone. The new halt proof does not remove that extra existential residue. It proves correctness at the exact E width, and thereby sharpens the next obligation to a regular block recoder **plus an exact-width interface**, not an unspecified invocation of MRDP.

The current [205-operation native compiler](grill_tag_native_composed205.md) is for the small program011, not the much longer compiled programs here. This packet supplies no new universal operation bound and no measured complete native SLP for these tables.

## 6. Reproducible evidence and limitations

The [receipt](grill_tag_halt_bridge.json) records:

- 64 exact complete-program specializations to the authenticated earlier two-symbol constructor, and384 encoding specializations;
- 928 local E→LR word-and-phase identities for all consistent nonhalt width choices, source phases, symbols and output pairs over alphabets of sizes2–4, including halt outputs;
- modular support checks at11 alphabet sizes,308 normal LR identities and462 shifted-erasure identities;
- 1,872 complete cleanup cases: alphabet sizes2/3, all nonhalt widths, every even word of length2/4/6 with one halt, and both normal phases;
- eight independent full FIFO first-empty traces: four valid `A→HA` source simulations and four `A→AH` cleanup-only cases outside the published Genera halt domain;
- 154 exact E-numeral/width identities,255 binary loader-port identities,77 retained four-bit E-prose discrepancies, and six malformed caller rejections.

The statements for arbitrary tables and lengths follow from the proofs above. The enumeration establishes only these finite implementation checks. No universal source program or arbitrary encoded input family has been exhaustively tested. No report or maintained compiler is modified.

Use standard Python, with the earlier pinned helper either alongside this source or under `--root`:

```sh
python grill_tag_halt_bridge.py --root /path/to/native-stream-queue \
  --expect grill_tag_halt_bridge.json
```

`--output` writes a fresh deterministic receipt. The checker uses no network, rejects optimized Python mode, authenticates the one imported reference's bytes before executing them directly, and compares saved JSON recursively with exact types. It never runs the inaccessible creator Perl code. All source executions are the locally reviewed helper or this standalone transcription.
