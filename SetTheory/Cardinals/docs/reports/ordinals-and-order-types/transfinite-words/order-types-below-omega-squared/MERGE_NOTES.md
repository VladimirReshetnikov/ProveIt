# Transfinite-word consolidation — 2026-09-29

Base snapshot: `5804c7aff`. A is the existing two-source
`order-types-below-omega-squared` report; B is
`finite-alphabet-transfinite-words`. The unified report contains three original
manuscripts; original sources and READMEs remain recoverable in Git. The archive
names and historical search dates are recorded in the README. Neither source
supplied a ProveIt pin; the snapshot is an editorial baseline.

## Scope and duplicate decisions

Both use finite poset alphabets, strictly increasing position maps with weak
label increase, strict ordinal length cutoffs and the same mutual-embedding
quotient. B's height-two formula is A's main theorem. Its binary values and
extremal characterization are already present. These statements occur once.
Common word definitions and classical order-type inputs also occur once.
B's derivation of the finite Higman input is kept as a proof of the existing
statement. Its residual identity and layered-product lemma are retained.

A remains the base for its selected-family classification (including the
universal-only exception), both amplification routes, exact-length strata and
canonical token algorithm. B adds the finite-height theorem and atom recurrence,
all of its indecomposable/protection lemmas, its induction, growth bounds,
enumeration and cycle-based symbolic implementation. The two proofs at height
two have different intermediate languages: A works on all selected-tail words;
B grows induced families of words ending in complete blocks. Neither proof was
silently replaced by the other. Both keep their exact finite computational
evidence and every stated boundary on formalization and priority.

The general theorem does not classify arbitrary selected families at higher
cutoffs or justify taking a supremum over heights. The elementary route avoids
the product-theorem import for A's main result only. It does not establish the
exact-stratum identities or replace that import in B's written induction.

## Notation and editorial corrections

B's W_k becomes V_k to distinguish it from A's W(P,F). B's J(P) equals A's
j(P); both include the empty ideal. o(X), embedding, ordinary and natural
arithmetic agree. B's absolute-value length macro is kept separate from A's
operator notation. Periodic nodes repeat maximal generators, equivalent to A's
all-elements blocks. Comparison exposed two imprecise sentences in A: every
element of a downset is *dominated by* a recurrent letter, not necessarily
itself recurrent when only maximal generators are repeated. Those sentences
are corrected without changing the definitions or proof. A's higher-cutoff
non-claim is scoped to its selected-family argument and now points to B's
full-language extension. No stronger selected-family theorem is inferred.

## Source-label concordance

Every existing destination label stays unchanged. Incoming document-local
labels map below: shared statements to the base, distinct material to `height:`.

| B label | Unified label |
|---|---|
| `sec:intro` | `merge:height-intro` |
| `thm:main` | `height:thm:main` |
| `eq:main` | `height:eq:main` |
| `eq:recurrence-intro` | `height:eq:recurrence-intro` |
| `cor:first` | `thm:main` |
| `eq:first` | `eq:main` |
| `cor:exception` | `height:cor:exception` |
| `sec:background` | `sec:prelim` |
| `eq:lengthmonotone` | `height:eq:lengthmonotone` |
| `eq:wqocalculus` | `height:eq:wqocalculus` |
| `eq:h` | `eq:finiteword` |
| `eq:higman` | `eq:finiteword` |
| `eq:power` | `height:eq:power` |
| `eq:amplify` | `height:eq:amplify` |
| `lem:layers` | `height:lem:layers` |
| `sec:atoms` | `height:sec:atoms` |
| `lem:onefactor` | `height:lem:onefactor` |
| `eq:evaluation` | `height:eq:evaluation` |
| `eq:heightlength` | `height:eq:heightlength` |
| `prop:comparison` | `height:prop:comparison` |
| `eq:leafleaf` | `height:eq:leafleaf` |
| `eq:leafnode` | `height:eq:leafnode` |
| `eq:nodeleaf` | `height:eq:nodeleaf` |
| `eq:nodenode` | `height:eq:nodenode` |
| `thm:normalform` | `height:thm:normalform` |
| `eq:count` | `height:eq:count` |
| `cor:upper` | `height:cor:upper` |
| `sec:blocks` | `height:sec:blocks` |
| `lem:equalblocks` | `height:lem:equalblocks` |
| `eq:equalblocks` | `height:eq:equalblocks` |
| `lem:nospill` | `height:lem:nospill` |
| `sec:activation` | `height:sec:activation` |
| `lem:marker` | `height:lem:marker` |
| `eq:marker` | `height:eq:marker` |
| `prop:activation` | `height:prop:activation` |
| `sec:separator` | `height:sec:separator` |
| `lem:separator` | `height:lem:separator` |
| `eq:separatorcondition` | `height:eq:separatorcondition` |
| `eq:separator-map` | `height:eq:separator-map` |
| `eq:separatorcount` | `height:eq:separatorcount` |
| `prop:amplification` | `height:prop:amplification` |
| `sec:mainproof` | `height:sec:mainproof` |
| `sec:binary` | `height:sec:binary` |
| `cor:extremal` | `cor:extrema` |
| `eq:extremal` | `cor:extrema` |
| `sec:computations` | `height:sec:computations` |
| `eq:antichaincount` | `height:eq:antichaincount` |
| `eq:idealcount` | `height:eq:idealcount` |
| `tab:counts` | `height:tab:counts` |
| `sec:scope` | `height:sec:scope` |
| `prop:width` | `height:prop:width` |
| `eq:widthbound` | `height:eq:widthbound` |
| `sec:audit` | `height:sec:audit` |
| `tab:verification` | `height:tab:verification` |
| `app:higman` | `height:app:higman` |
| `app:decision` | `height:app:decision` |
| `eq:symbolic` | `height:eq:symbolic` |
| `eq:cyclecondition` | `height:eq:cyclecondition` |

## Byte-preserved supporting files

| Former path in B | Destination path |
|---|---|
| `code\atoms.py` | `code\heights\atoms.py` |
| `code\omega_words.py` | `code\heights\omega_words.py` |
| `code\verify.py` | `code\heights\verify.py` |
| `data\atom_counts.csv` | `data\heights\atom_counts.csv` |
| `data\atoms_A2_k1.json` | `data\heights\atoms_A2_k1.json` |
| `data\atoms_A2_k2.json` | `data\heights\atoms_A2_k2.json` |
| `data\atoms_A2_k3.json` | `data\heights\atoms_A2_k3.json` |
| `data\atoms_A3_k1.json` | `data\heights\atoms_A3_k1.json` |
| `data\atoms_A3_k2.json` | `data\heights\atoms_A3_k2.json` |
| `data\atoms_A3_k3.json` | `data\heights\atoms_A3_k3.json` |
| `data\atoms_C2_k1.json` | `data\heights\atoms_C2_k1.json` |
| `data\atoms_C2_k2.json` | `data\heights\atoms_C2_k2.json` |
| `data\atoms_C2_k3.json` | `data\heights\atoms_C2_k3.json` |
| `data\atoms_C3_k1.json` | `data\heights\atoms_C3_k1.json` |
| `data\atoms_C3_k2.json` | `data\heights\atoms_C3_k2.json` |
| `data\atoms_C3_k3.json` | `data\heights\atoms_C3_k3.json` |
| `data\verification.json` | `data\heights\verification.json` |
| `proof_audit.md` | `03-heights-proof_audit.md` |
| `references.bib` | `data\heights\references.bib` |
| `source_status.md` | `03-heights-source_status.md` |

Original audit paths describe the delivered package. Use the live README for
commands. See the collection CONSOLIDATION.md for fresh validation evidence.
