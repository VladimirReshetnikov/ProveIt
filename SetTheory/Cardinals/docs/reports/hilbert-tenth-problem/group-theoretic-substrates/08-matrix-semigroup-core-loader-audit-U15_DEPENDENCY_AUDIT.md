# U15 finite-input and r.e.-completeness dependency audit

Audit date: 2026-10-03. Scope: read-only inspection of the supplied releases and primary PDF; no upstream Python was imported or executed, and no prior release was edited.

## Bottom line

The finite binary tape halting language of the pinned Table 16 machine, started in `u1` scanning `c=0`, is many-one r.e.-complete by the effective halting-preserving simulations in Neary--Woods. This is a corollary of the published constructions, not a separately numbered theorem explicitly called “r.e.-completeness.” The implementation in Report 16 begins at a finite tape. The full arbitrary-TM/program-and-input compiler remains a published dependency. An explicit **bi-tag table/dataword to U15 tape encoder** is present as inert upstream source evidence, but it is not the missing TM-to-bi-tag compiler.

Report 23 is useful for documenting an explicit ordinary-input frame, but its large conditional Grill/polynomial theorem and native arithmetic dependencies are unnecessary to establish the input hardness used here.

## 1. Exact machine and accepted input domain

Let `U` be the 29-defined-transition, 15-state, 2-symbol machine of primary Table 16. Identify `c=0`, `b=1`, and `A,...,O=u1,...,u15`. Its sole undefined transition is `(u10,b)`, i.e. `J1`. The `(u10,c)` cell is defined as `b L u11`. The prose sentence at the end of Section 3.5 names `c` in error; the literal transition table is unambiguous.

For arbitrary finite words `ell,r in {0,1}*`, initialize `U` in `u1`, head at coordinate 0, with cell 0 equal to 0, cell `-i-1` equal to `ell[i]`, and cell `i+1` equal to `r[i]`. All unlisted cells are zero. Both halves are nearest-head-first. Define

    H_U = {(ell,r): this initialized U eventually reaches J1}.

This all-finite-tapes language is the correct source language for a finite-tape target encoder. It includes malformed program encodings, whose behavior need not be characterized by the universality theorem. Hardness uses only the following proper well-formed subfamily.

For a finite bi-tag program `B` with encoded program `P=<B>` and encoded dataword `D=<data>`, choose no optional `S` padding in primary equation (3). The physical finite tape is

    P b [c] D

where brackets mark the initially scanned cell, not tape characters. Thus

    ell = reverse(binary(P b)),  r = binary(D),

with `binary(c)=0` and `binary(b)=1`. The head cell is omitted from both halves. Both tails are blank. There is no infinite periodic background.

For a source TM input, use the bi-tag configurations actually produced by the clockwise-TM construction, retaining both right and left blank-boundary symbols. This avoids broadening the claim to any malformed or pathological arbitrary bi-tag dataword. One can additionally use the padded equal-block source convention from the pinned initialization note: for a selected semidecider of a c.e. subset of positive integers, the initial dataword is

    e1 pair(w) a_right a_left,

where bit 0 is `(a2,a1)` and bit 1 is `(a1,a2)`. Put

    A_i = (cb)^(8i-5) bb,
    B_0 = A_2 A_1,  B_1 = A_1 A_2.

Both bit blocks have 32 physical tape symbols. In Report 23's convention, `w` is the canonical LSB-first spelling of `x+1`, for positive `x`; its length is at least two. The exact right word is

    (cb)^(8 q_B) B_w0 ... B_w(n-1) A_right A_left.

The exact left half is still `reverse(P b)`. The program/alphabet/boundary indices are fixed for a selected semidecider. This subfamily alone is enough for c.e.-hardness.

## 2. Published theorem chain and many-one conclusion

Published source: T. Neary and D. Woods, *Four Small Universal Turing Machines*, Fundamenta Informaticae **91(1) (2009), 123--144**, DOI `10.3233/FI-2009-0036`. The published metadata is verified at https://journals.sagepub.com/doi/10.3233/FI-2009-0036 and https://dna.hamilton.ie/woods/. The reading PDF used for the detailed inspection is at

https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf

All printed page numbers below are specific to the downloaded author/draft PDF, whose pagination is 105--126. Its draft DOI metadata and pagination are not the authoritative published bibliography. The exact downloaded-PDF locators are preserved for reproducible table/proof inspection. The distribution archive links the reading source instead of embedding its copyrighted PDF cache.

1. **Lemma 2.1**, printed pp. 108--109: effective construction of a clockwise machine `C_M` simulating an ordinary deterministic one-tape TM `M`; its proof explicitly gives the rules and says the input transformation is a finite-state transduction. Standard effective normalization gives the stated restrictions: no blank input letters, no writing the external blank, and one final state. The simulation retains two finite boundary markers for the infinite blank tails.
2. **Lemma 2.2**, printed pp. 110--111: explicit effective clockwise-machine to bi-tag transformation, with `ex ai -> aj ey` or `ex ai -> aj ak ey`. The proof explicitly preserves halting via the corresponding `e_h` becoming the leftmost symbol.
3. **Theorem 2.1**, printed pp. 111--112: composition of the above simulations, with polynomial simulation overhead. The computational overhead is not needed for a computable many-one reduction.
4. **Definition 3.1**, equations (3)--(4), **Tables 1--3**, printed pp. 112--113: effective finite program and dataword encoding. For U15, `G=bc`, the initial head scans its rightmost `c`, the initial state is `u1`, and the blank is `c`.
5. **Theorem 3.1**, printed p. 117: proved explicitly for U9,3, including its halting behavior. The paragraph immediately after its proof states that the correctness proof applies to the remaining machines. **Section 3.5**, printed pp. 120--123, gives the U15 cycles, **Table 16** on p. 121, and its halting mechanism on p. 123. Therefore cite this complete chain; do not falsely label Theorem 3.1 alone as a specifically stated U15 theorem.

The constructions are uniform finite recipes in `M` and its finite input. Hence there exists a total computable encoding `C(M,w)=(ell,r)` on a standard effective domain of valid TM/input codes such that

    M halts on w  iff  C(M,w) in H_U.

Malformed numerical program codes can be assigned to any fixed nonhalting source computation if a total function on all natural numbers is desired. This gives `K <=_m H_U` for the ordinary halting set `K`. Conversely `H_U` is c.e.: directly simulate the fixed finite transition table and accept on its sole undefined transition. Thus `H_U` is **many-one r.e.-complete**, not merely undecidable. No effective complexity bound on writing the eventual matrix target follows from this statement.

The conclusion uses the published simulation proof as a mathematical dependency; the current audit is not an independent proof-assistant verification of all its unbounded cases. Bounded tape experiments do not replace that dependency.

## 3. What is actually materialized

### Report 16

`prior-artifact:literal-reversible-source-release-20261003/sections/02-frontend.tex`, lines 28--55, explicitly limits the implemented interface to finite binary tape and explicitly calls arbitrary-program initialization a published dependency.

`prior-artifact:literal-reversible-source-release-20261003/source/loader.py`, lines 12--23, implements exactly

    L = sum(ell[i] 2^i), R = sum(r[i] 2^i),
    from_tape(ell,r) = (START, 2^L 3^R, 0).

No program interpretation, program-to-bi-tag compilation, or halting simulation appears in this function. It is a total mathematical map on finite binary words, subject in actual execution to available resources. Trailing zeros at the far ends of either word represent the same tape and the same integers; injectivity of spelling is neither present nor needed.

### Explicit bi-tag encoder in frozen scientific evidence

`prior-artifact:grill-universal-input-research-20261003/literal/upstream_u15_builder.py.txt` contains:

- lines 65--73: `a_code`, `bit_blocks`
- lines 76--100: `bts_program(q,h,productions)`, implementing Tables 2--3 and equation (4)
- lines 103--116: `encoded_configuration(q,h,productions,data)`, returning `contents=P+'bc'+D` and `head=len(P)+1`
- lines 136--150: `program_parameters`, for a bi-tag table already supplied by the caller

The `productions` argument already supplies every `(e_j,a_i)` production, `j<h`, and `data` already supplies the tagged input word. This is **bi-tag -> U15**, not TM/program -> bi-tag -> U15. The file has external imports and is retained as inert evidence; this audit did not execute or import it. The same frozen file appears inside Report 23's reproducibility tree.

`prior-artifact:grill-universal-input-research-20261003/literal/upstream_u15_proof.md`, Section 2, states “Apply the primary source's effective M -> C_M -> B_M constructions.” It does not supply a runnable implementation of that compilation.

### Report 23

`prior-artifact:universal-grill-exact-degree-release-20261003/article/report23.tex`, lines 100--119, explicitly treats finite-input universality as an import; lines 123--161 specify the concrete U15 frame and equal-length blocks.

The locally replayable `reproducibility/replay_code/arithmetic/input_loaders.py` emits the paid arithmetic relation from `x` and already supplied valid per-program parameters. It does not construct those parameters from an arbitrary source program. The five program parameters remain a selected-language slice, rather than an executable arbitrary-program compiler.

**Materialization conclusion:** the arbitrary-program end-to-end compiler is not implemented in these inspected artifacts. Its effective existence is justified by the cited primary constructions. The last bi-tag-to-U15 stage is explicit source evidence and the finite-tape-to-counter stage is runnable local code.

## 4. Minimal honest theorem for the new target encoder

The clean local theorem should be stated without pretending to have an executable compiler from arbitrary source code:

> Fix the pinned Table 16 machine U and the finite-tape initialization above. The released encoder is a total computable map E from two finite binary tape halves to target matrices. For every such pair, U halts from that initialization if and only if E(ell,r) belongs to the fixed semigroup generated by the released matrices.

Then the end-to-end corollary is:

> By the effective finite-input universality construction of Neary--Woods, H_U is many-one r.e.-complete. Therefore H_U <=_m Membership(G) via E, and composing with the published compiler gives K <=_m Membership(G). Since products of a fixed finite family of integer matrices can be enumerated and compared exactly with a supplied target, Membership(G) is c.e.; hence it is many-one r.e.-complete.

Use the semigroup's declared nonempty-word convention, or its declared monoid convention, consistently in the local equivalence and enumeration. This audit does not verify that new equivalence; it establishes the source/input dependency the parent construction may compose with it.

Suggested disclosure in the paper:

> The release materializes the finite-binary-tape-to-target map. The effective reduction of an arbitrary Turing-machine computation to that input family is the published Neary--Woods dependency. We do not claim to have reimplemented that full compiler.

This statement permits a genuine end-to-end mathematical many-one completeness theorem while accurately limiting the software deliverable. It must not be described as a fully materialized arbitrary-program-to-matrix compiler, an independent new proof of U15 universality, or a polynomial-time reduction merely because every step is computable.

## 5. Evidence pins and visual checks

SHA-256 values read during this audit:

| File | SHA-256 |
|---|---|
| primary `neary-woods-2009.pdf` | `6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b` |
| inert `upstream_u15_builder.py.txt` | `cb3098d854a2599648bf5edfedcc91febef50ad223a4b864b97c63356cb6e39e` |
| Report 16 `source/loader.py` | `c371be6b8f7382fb351821f66c86591467195250e41759eb9240e00321e2be08` |
| Report 16 `source/dependency/tm_table.json` | `0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a` |

Visually inspected the saved primary images for printed pp. 112 and 121, confirming the head position, blank/start conventions, U15 Table 1 constants, and the undefined `J1` cell. Text of the surrounding constructions and halting paragraphs was inspected from the saved PDF text extraction. No upstream computational checks were run in this audit.
