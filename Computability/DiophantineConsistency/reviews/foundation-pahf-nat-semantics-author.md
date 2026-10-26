# Standard-natural semantics of the existing Foundation/PAHF maps

Author: `circuit_reduction`. Status: the two new leaves are frozen after full
source review and successful private, sequential Lean replay. This is a
standard-ℕ semantic result, not an HA proof of a formula and not a completed
consistency calibration.

The final files are:

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/FoundationPAHFNatSemantics.lean` | 127 | `117aad800f50185ac5187afa196d3b48fbb391bf8337a56acfe82cb6e688341a` |
| `Lean/DiophantineConsistency/FoundationPAHFNatSemanticsChecks.lean` | 53 | `986bc7abfed2ca345b09c9f0635c6022e4eccb0fe0187ed2d7d60e18810c2710` |

`sat_sentence_GG φ ee` says that PAHF satisfaction of the existing syntax map
applied to the existing Foundation GG translation of an arithmetic sentence
is equivalent to that sentence's Foundation truth in standard ℕ. The target
structure is exactly `ArithmeticExpression.semiringStructure ℕ`; the source
uses Foundation's actual natural ordered-arithmetic structure.

The proof first evaluates every translated term under explicit bound/free term
environments. Its strict-order case proves the positive-difference witness
`∃d, a+(d+1)=b` equivalent to `a<b`. The two lift lemmas then retain all
ambient terms under a binder. A structural induction proves truth preservation
for the already defined GG expression, including its negative encodings of
disjunction and existence. No replacement GG algorithm is defined. The source
search found no existing semantic theorem for this particular composite map.

The closed theorem obtains environment independence from Foundation's actual
empty-free-variable embedding. Focused checks include zero/equal-input order
boundaries, falsehood, different target free environments, and a two-binder
formula whose exact surviving bound/free condition is `ee 7 + 1 = ee 15`.
That last check fixes the two source bound-slot orientations and the preserved
free-term offset, rather than merely asserting that a formula with witnesses
is true.

The fresh commands were the private replay driver's `run` commands, each
invoking Lean 4.32.0 with `-M6000 -j1 -DElab.async=false` and no changed proof
budgets. The final main completed in 2.74 seconds with an empty log; the final
checks completed in 1.90 seconds. All seven named axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Choice in the semantic theorem
is intentional classical metatheory; it is not a new HA deduction rule.

The private object directory is
`/tmp/foundation-pahf-nat-semantics-vtmecspi/lib`. Main/check object hashes are
`a565f21f107515af5eae53800ae3467addc5c1d34f34081f3c03264a9941964d`
and `c584b581b98c7b5a0a4176fa9cb21f8a509306ec3c396d78dad0c592852690d8`.

The exact prerequisite closure contains 82 reused custom modules, including
70 Foundation modules, all selected transitively from the accepted
`foundation-ha-current-transfer-dependency-replay.json`. There are 38 direct
package/toolchain object boundaries and 483 pinned inputs. Every selected
source/object/recorded companion/trace was checked before and after execution;
the toolchain and package identity and 512 MiB free-space reserve were checked
as well. No Foundation, old native, or package closure was freshly rebuilt.
Only the two displayed leaves were freshly checked. The durable manifest is
`foundation-pahf-nat-semantics-dependency-replay.json`, SHA256
`b008b3b9564041b534fbf5078a1c1cbef429ebdd725e92f409da52422a3c4754`.
The complete driver, input inventory, snapshots, logs, and per-run records are
in `foundation-pahf-nat-semantics-author-replay/`.

Two failed main elaborations are retained. The first needed explicit unfolding
of the semantic hom's application, explicit function-symbol cases, and removal
of a redundant dependent generalization. The second was a Lean layout issue
at the universally quantified induction hypothesis, fixed by parentheses.
An earlier successful checks snapshot is retained alongside the final stronger
nested-binder check. No theorem premise or conclusion was weakened.

The fixed `GG(ZFC.consistent)`/actual-`BProv` standard-Nat comparison is not part
of these two files. Its separate dependency audit has uncovered unexecuted old
endpoint providers; no missing object is treated as checked. Even a completed
standard-Nat comparison would not prove HA equivalence to an untranslated
proof-checker formula or supply the still-missing PA proof of the current
equation/consistency equivalence.
