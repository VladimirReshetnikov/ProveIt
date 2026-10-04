# Independent review of the ant48 occurrence-component cleanup

**PASS; no requested correction.** This review covers the complete emitted
7,818-row component, its 24 output identities, local liveness, and the derived
complete-grammar deltas. It does not emit or rehash the multimillion-gate full
stream, rerun an ant simulation, or certify additional physical or
number-theoretic theorems.

Reviewed author files:

| File | SHA256 |
| --- | --- |
| `ant48_rotated_occurrence_cleanup.py` | `cf260d28a695b0c723f006dd85f6ec1517ca8f9a74e80e8ff080f411a52426fe` |
| `ant48_rotated_occurrence_cleanup.json` | `a7b914e403b9f8f71cdaea4b39307447f246249a11412fc6e2cd3e4d5ac4878c` |
| `ant48_rotated_occurrence_cleanup.md` | `9d72680e7a37051709a7e9f807dc58896c7eca9f2f6a8b03675389c0114f098e` |

The complete author helper and companion were read. All four declared parent
pins were checked independently. In particular the frozen parent occurrence
JSON is `a48ada7ad9e168c5ad3154ad9cfffeacc9286d799ad4481079401b7574da96b7`;
its Python was not imported or run. The endpoint receipt is
`b2dd16ebbe9f89adc85a161a897d9c86009233ac90a1e8214bb5879cc4c7cb98`.

Starting from parent JSON only, a separate fresh reconstruction retained the
original register names, propagated known-zero aliases, and independently
cached commutative operator/operand pairs. It found exactly 32 add-zero
removals, four multiply-zero removals, and 32 repeated-expression removals.
After deterministic renaming of retained registers, all 7,818 author rows and
all 24 output aliases matched exactly. Every entry and target in the author's
68-event transcript also matched this independent reconstruction.

Each rewrite is an identity in a commutative ring under the actual inherited
binding `paid_zero=1-1`. Zero is not an arbitrary new input constrained by an
extra equation. Alias propagation points only to inherited ports or earlier
retained rows, and commutative CSE uses exact operator/operand keys. Induction
therefore proves equality at all 24 component outputs. A separate sparse
coefficient interpreter expanded the independently reconstructed DAG over Y
and the occurrence indeterminates. All outputs matched

    sum(s=0..956) T[kind,s] * Y^((480-b-s-phase/600) mod960)

coefficientwise: 24 polynomials and 22,968 terms. This proves polynomial
equality, including Y=0,1,-1, without division or an assumption Y^960=1.
The residue expression selects an ordinary nonnegative exponent.

All retained rows are in the output dependency closure. The sole unused old
binding is `paid_zero`; the new component uses exactly 3,829 inherited ports:
Y and all 3,828 occurrence coefficients. Its old zero producer remains paid in
the full prefix. No additional global dead-code saving is inferred.

The independent count is **7,818=3,930M+3,888A**. The four zero products and
16 repeated products save20M; the 32 zero additions and16 repeated additions
save48A. Thus the claimed extra68 gates and total38,214-gate saving from the
original 24 Horner chains are exact. Keeping the unchanged24 products and22
phase additions gives3,954M+3,910A=7,864 for the complete rotated stage.

Subtracting only this verified delta from the pinned whole-grammar ledgers
gives14,620,720 /14,620,730 for two/one raw inputs. Composing with the disjoint
nine-multiplication endpoint splice gives **14,620,711 /14,620,721**. Both
M/A splits in the author table were checked. These are complete-grammar
ledger consequences, not newly generated complete-stream hashes. The
unchanged consumers and finalizer preserve the full polynomial, its465/467
positive witnesses, one equation and inherited exact degree2,304,000.
The established universal84 bound is unaffected.

A fresh authorized execution of the new helper from `/`, using installed
pinned parents and `--expect` against the exact author receipt, passed.
This review did not execute parent/archive code. Its independent reconstruction
and coefficient checks are distinct from that replay. No repository or frozen
predecessor files were modified.
