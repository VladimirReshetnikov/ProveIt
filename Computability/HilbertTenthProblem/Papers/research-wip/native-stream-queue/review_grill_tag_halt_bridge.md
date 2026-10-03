# Independent review of the corrected Grill halt bridge

**PASS after an example-scope clarification.** The general cleanup proof is sound for every stated finite alphabet/table, both normal source phases, and an even produced word containing exactly one halt symbol. Together with the normal E/L/R identities it proves the claimed halting equivalence on valid Genera executions at the exact corrected encoded width. It does not solve the ordinary-input decoder or the known existential-padding problem.

The frozen author Python is `3984312d5a5d9c8ebfde557e683e32bcba7fc69dbf65cfe1a9037803eebdb892`, receipt `94f1e283b27c5bb3b4009fb49a64a8fcf2fd3b7d6041088fec38f277deaed767`. I read the complete source and companion note. The final note, including the clarification below, is `aadb23584cc560ef13b2e2269cda177e4211e27602a25be4e346b98c90a3ebd7`. No source or receipt correction was necessary. The independent checker authenticates the Python, receipt and original reference bytes before executing the reviewed new module; it does not call the author's verify function or repeat its full suite.

## General proof check

Put a=28(N+1). Modulo7a the possible nonzero run locations are odd and lie in three disjoint intervals: [17,a−35], [a+13,2a−39], and [2a+3,5a/2−13]. Within each interval the literal spacing prevents collisions. Shifting any active location by3a puts it in [3a,11a/2), which is disjoint from all active locations and does not wrap modulo7a. Since a is even, the shift preserves parity.

In each E, L and R block, the ones of all variable grills occur at even offsets; only the small fixed grill has odd one positions, exactly at the intended active slots. The extra `(10)` repetitions in L also start at an even offset. Therefore shifting a block's start by3a changes every one into an exponent-zero step. This covers the extended halt L/R blocks and the E_H* intermediate: its extra material is only trailing zeros. The argument covers variable grills that cross whole run-table periods, not merely a short substring.

At a normal phase, the seven active E outputs concatenate to the exact L/R blocks of the two produced symbols, including halt outputs. The three normal L/R active outputs concatenate to E, or to E_H* for the halt symbol. The corrected second E grill has a−4 ones; the published a−2 wording would add four bits and break phase alignment. The new note expressly retains this correction rather than certifying the erroneous prose.

An E block advances phase by7a*w modulo14a. A normal L/R block always has length7a modulo14a. Because each source production has exactly two outputs, every nonhalting L/R generation has an even number of blocks and adds zero phase modulo14a. Thus the phase retained between whole E generations is exactly the persistent Genera phase; it is not reset incorrectly at a generation boundary.

For a produced even word with one H at index j, prefix L/R blocks operate at normal phases and produce their E encodings. The H block has length10a rather than7a modulo14a, introducing precisely3a of phase displacement. Its output is E_H*, with length17a/2. All later L/R blocks are erased to zero-only words. The complete L/R generation length is3a modulo14a, so the next generation starts shifted by3a. Every prefix E block has length0 or7a modulo14a, keeping that shifted alignment until E_H*. These blocks and E_H* are erased. Any different phase reached after E_H* is harmless: the remaining suffix was already zero. The output is exactly2a(j+1) zeros, and the following generation empties it.

The three displayed cleanup lengths are positive and account for every initial-generation bit. A FIFO cannot become empty while a nonempty unprocessed part of that generation remains. At the first two boundaries the computed next word is nonempty. Therefore their sum is the exact **first** empty time, not merely an upper bound.

If no source generation ever produces H, both encodings stay nonempty and the normal identities give infinitely many nonempty FIFO generations. If a valid source generation produces its unique H, the cleanup proof gives finite first halt. The required nonempty initial source word and two-output productions exclude the creator's empty-word/nonhalting corner case. Initially halted and multiple-halt source words remain outside the theorem.

## Resolved example-scope issue

The primary [Genera semantics](https://esolangs.org/wiki/Genera_Tag) requires not just one H, but also that hypothetically processing the preceding prefix would not produce another H. I reopened that page and the [Grill construction](https://esolangs.org/wiki/Grill_Tag); their live footers still identify revisions182460 and181950. The permanent-link endpoints were unavailable through the browsing tool, so this read used the live pages and verified those footer identifiers. The external Perl compiler was not accessed or executed.

The author's four `A→HA` FIFO examples satisfy the halt convention because the preceding prefix is empty. Its four `A→AH` examples do not: their preceding A would produce another H. They are nevertheless valid tests of the stronger **one-H cleanup lemma**, which does not need that prefix condition. Root independently raised this distinction; I confirmed it and requested an explicit sentence. The author added it both near the examples and in the receipt-scope list. The code, trace values and main theorem need no change. The review receipt separately counts four valid whole-simulation examples and four cleanup-only examples outside the source's defined halt interface.

## Encoding and arithmetic scope

The E numeral factorization follows by ordinary concatenation in little-endian order. Its width-dependent adjustment consists entirely of trailing zeros, so the same numeral alone does not identify the encoded block width. The formula for a full word must therefore retain both its numeral X and the exact power P0 determined by all block widths.

For a width-one binary input alphabet, `D^b=1+(D−1)b` for b∈{0,1} gives `X=A[J+(D−1)R]`. Conditional on a genuine regular recoder's R,J,P0, this costs exactly two multiplications and one addition; the weak slack `P0−X` adds one subtraction. The four-operation claim is only this literal interface. The recoder, canonical binary-length condition, equality of the native initial width with P0 and full finalizer are not paid by those four gates. All nonempty E words have at least two trailing zero bits, so `0<3X<P0`; the cone itself is not the missing condition.

The independent checker retains the earlier obstruction in the generalized compiler: the nonhalting two-symbol all-zero production table has exact E input whose normal generations double, but adding six zero bits gives the same numeral and first halt2274. Consequently proving this new halt bridge at the exact width does not validate an existential choice of initial width. No specific universal Genera table or decoder is provided, and the205-operation011 native example is not a measured source for these long compiled programs.

## Independent bounded evidence

The portable checker separately constructs complete run tables, bit blocks and a FIFO interpreter. It checks new alphabet sizes and arbitrary halt-symbol indices, including0 and interior labels, rather than assuming H is last. Its deterministic receipt reports:

- 33 complete table identities and table-size/positive-run counts;
- 441 literal E/L/R blocks,882 whole-block shifted-support checks,588 normal L/R word identities and228 E word/phase identities;
- 198 complete cleanup cases on lengths2,4,8 and both normal phases;
- 132 nonhalting two-generation simulations with odd-length initial source words and persistent phases;
- Eight new valid whole-source FIFO first halts at alphabet size5;
- 63 canonical binary conditional-loader identities, including exact widths and the strong cone;
- The retained same-numeral padding counterexample and the4/4 classification of the author's fixtures.

These bounded checks support the implementation; the modular/parity and generation arguments above supply the general theorem. They do not instantiate a universal source or establish an unrestricted arithmetic optimum. The fresh independent saved-receipt replay passed. No report, archive, maintained compiler or Git state was modified.

Reproduce using the standard library:

    python review_grill_tag_halt_bridge.py \
      --source grill_tag_halt_bridge.py --receipt grill_tag_halt_bridge.json \
      --root /path/to/native-stream-queue \
      --expect review_grill_tag_halt_bridge.json

`--output` writes an independent deterministic receipt. Input pins are checked before execution and saved JSON is compared recursively with exact types. The published reference helper must exist under the supplied root, although this independent review does not execute it.
