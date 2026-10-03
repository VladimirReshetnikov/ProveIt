# A fixed directed semigroup with 193 literal SL4(Z) generators

The [complete array and receipt](group_directed_semigroup193.json) give a fixed **193-generator directed semigroup** with the same finite-U15-input target map as the incoming 229-generator construction. Membership remains many-one r.e.-complete under the same published U15 simulation dependency. This is a matrix-generator reduction; it gives no Diophantine arithmetic-operation bound, subgroup presentation, ordinary-affine input loader, or optimality claim.

The change is to use the irreducible terminal word `[J1]`, keeping both boundary brackets. The old fresh symbol X and the halt-conversion and bracket-erasure rules are unnecessary. Four context-copy tiles suffice on every valid derivation. The [standard-library helper](group_directed_semigroup193.py) reconstructs the complete array from pinned archive data; it executes no archived Python, builder, or test suite.

## 1. Frozen predecessor and unchanged input

The predecessor is [Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip](../../../../../docs/incoming/Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip), SHA256 `b494c2b8e516d811cbecf305a748197af2a565882319a86586fec316c5ba8c47`. The helper pins five members below its `universal-matrix-report32-release-20261003/` prefix: the entire core proof, the U15 dependency audit, the literal semigroup array, the 30-cell machine table, and the accepting witness. Their full hashes are embedded in the helper and receipt.

For finite binary words ell and r, both nearest-head-first, initialize U15 in state A scanning zero, with ell on its left and r on its right and blank-zero tails. The unchanged configuration word and matrix target are

    w(ell,r) = [ reverse(ell) A 0 r ],
    T(w) = diag(Phi(w#)^(-1), t).

The machine table, input spelling, upper letter codes, lower index codes, and target formula are unchanged. In particular this is the same finite-blank-tape input convention, not a periodic background or a new ordinary integer encoding. The arbitrary-TM-to-U15 input compiler remains the mathematical dependency recorded in the archived `core/PROOF.md` Section8 and `core/loader-audit/U15_DEPENDENCY_AUDIT.md`; this helper does not implement or re-audit that compiler.

## 2. The 91 rules and the finite-input theorem

Keep all 87 machine rules generated from the 29 defined transition cells. A right move `(q,a)→(b,R,p)` has

    qa0→bp0, qa1→bp1, qa]→bp0].

A left move has

    0qa→p0b, 1qa→p1b, [qa→[p0b.

Retain the old rule indices 1 through87. Delete old rule88, `J1→X`, and old rule93, `[X]→X`. Replace the four binary cleanup rules, keeping their old indices 89 through92, by

    0J1→J1, J10→J1, 1J1→J1, J11→J1.

The terminal is the four-letter word `[J1]`. There are 19 active rewrite letters: two tape bits, fifteen states and two brackets. X is unused.

A live word `[l q a r]` contains exactly one state symbol. Away from J1, the scanned cell and the adjacent tape bit or boundary enable exactly one machine rule. It produces the correct next finite configuration, extending a blank cell only when the head crosses an endpoint. None of the four cleanup rules can apply: each requires the unique state to be J scanning1. The table has no outgoing transition at J1.

Once J1 is reached, only cleanup can apply. Each cleanup removes exactly one binary letter immediately to the left of J or to the right of its retained scanned1; it preserves J1 and both brackets. There are no machine transitions from any resulting `[l J1 r]`. Erasing all of l and r reaches `[J1]`, on which no rule applies. Conversely any valid-input derivation reaching `[J1]` must first reach the J1 halting cell, since cleanup cannot begin earlier. Thus

    U15 halts on (ell,r) iff w(ell,r) →* [J1].

This proves the finite-input statement for arbitrary finite ell,r, not just the saved example. It needs no assertion about arbitrary malformed starting words.

## 3. Restricted copies and the correspondence equation

Keep only four copy tiles `(a,a)`, for `a∈{0,1,[,]}`. Keep the 91 rewrite tiles `(rhs,lhs)` and the separator tile `(#,#)`. The complete inner tile count is

    4 + 87 + 4 + 1 = 96.

Preserve the original tile identifiers. The retained IDs are `1,2,18,19`, `21..107`, `109..112`, and `114`. The deleted IDs are `3..17,20,108,113`. There is no renumbering of the lower free generators.

In every valid machine or cleanup step, the rewritten substring contains the unique state. Its left and right contexts contain only binary letters and brackets. The four surviving copy tiles therefore spell every required context. A derivation `w=w0→...→wd=[J1]` gives one tile block per step: copies for the left context, its rewrite tile, copies for the right context, then separator114. Concatenating the blocks gives

    h(s)=w1#...wd#, g(s)=w0#...w(d−1)#,
    w# h(s)=g(s) [J1]#.

The reverse implication needs no missing copy tile. Split any tile word at separator occurrences. No other tile contains #, and every side is nonempty. Comparing final #-segments forces its last nonseparator block to be empty. Comparing the remaining segments yields a chain starting at w and ending at `[J1]`. Within each block the tile sides partition the current word into copies or directed rule applications on disjoint substrings. Serializing those applications left to right gives a genuine derivation. Thus any solution of the equation implies `w→*[J1]`, even before restricting w to a live input.

Only the forward direction for valid finite input words is needed and claimed here. It has just been proved using their actual context alphabet. The packet does not reuse the parent's stronger all-malformed-word correspondence claim merely by deleting state-copy tiles.

## 4. Literal matrices and unrestricted positive products

Use the original matrices and codes:

    P=[[1,2],[0,1]], Q=[[1,0],[2,1]],
    E_j=Q^(-j) P Q^j=[[1+4j,2],[-8j²,1−4j]].

The old upper codes map `0,1,A,...,O,[,],X` to1 through20 and # to21. They remain unchanged; X's unused code20 is retained only in the legacy code dictionary. The active top alphabet has 20 letters including #. The lower marker is `t=E_0` and tile i retains `x_i=E_i`, including the original largest index114.

For each retained tile i emit

    A_i=diag(Phi(h_i),x_i),
    B_i=diag(Phi(g_i)^(-1),t^(-1)x_i^(-1)t).

Emit the changed terminal generator

    C=diag(Phi([J1]#)^(-1),t).

All 193 full integer matrices are in the receipt, ordered by ascending retained A indices, ascending retained B indices, then C. All whole-word inverses use the determinant-one matrix inverse, not an incorrect forward list of letter inverses. No inverse generators are adjoined to the semigroup.

The original ping-pong proof makes P,Q a free basis; distinct conjugates E_j freely generate. Expanding a reduced word in distinct E_j leaves alternating nonzero P powers and nonzero interior Q powers. Removing some indices preserves this freeness. In particular the sparse lower indices present no issue.

For completeness, the lower-marker argument remains unchanged. The exponent sum of t makes a positive generator word with lower value t contain exactly one C. In the kernel basis `y_(i,h)=t^h x_i t^(−h)`, B before C contributes only negative height−1 letters and A after C contributes only positive height+1 letters. Neither has a possible inverse occurrence, so neither can appear in a word with lower value t. The remaining height-zero positive and negative parts cancel exactly in reverse order. Hence the unrestricted positive product must be

    A_(i1)...A_(id) C B_(id)...B_(i1), d≥0.

Its upper value equals T(w) precisely when

    Phi(w# h(s))=Phi(g(s) [J1]#).

The upper embedding converts this to the literal positive-word equation of Section3. Together with Section2 this proves, for the fixed semigroup S193,

    T(w(ell,r))∈S193 iff U15 halts on (ell,r).

The d=0 case is the nonempty product C for w=`[J1]`; no identity or empty-product generator is introduced. Main-interface inputs start in A and are not this terminal word. Enumerating nonempty products semidecides membership. The inherited U15 many-one completeness theorem and the unchanged computable target map therefore give many-one r.e.-completeness for this one fixed matrix semigroup. This conclusion is about directed semigroup membership, not a matrix subgroup predicate.

## 5. Complete resources and coefficient tradeoff

| Resource | Incoming parent | Successor |
|---|---:|---:|
| Machine rules |87|87|
| Additional rules |6|4|
| Copy tiles |20|4|
| Total inner tiles |114|96|
| Distinct SL4(Z) generators |229|193|
| Matrix entry slots |3664|3088|
| Nonzero entry slots |1831|1543|
| Maximum absolute entry |63038000|1304111120|
| Maximum magnitude bits |26|31|
| Sum of entry magnitude bits |21372|19321|

Magnitude bits mean `bit_length(abs(entry))`, with zero contributing zero. They exclude a separate sign bit and are not a serialization or compressed-description count. Every new matrix has determinant one and the numerical arrays are pairwise distinct. Of the retained matrices, 184 are unchanged. Exactly the four cleanup A/B pairs and C change their upper blocks; all retained lower blocks are unchanged.

The larger maximum comes from C, whose upper inverse is

    [[−30624767,−862202],[1304111120,36715617]].

Thus fewer generators do not imply smaller individual coefficients or an unconditional complexity improvement. The input target formula and its original linear output-bit bound are unchanged because its letter codes and word length are unchanged. No claimed elementary arithmetic cost is inferred from the number of generators.

## 6. Actual accepting product and bounded verification

The archived finite input has nearest-first left word `011` and empty right word. Its initial configuration is `[110A0]`. Seven actual machine steps reach `[J111010]`. Removing the old J1→X step and the old final bracket erasure leaves five binary cleanups, for twelve total rewrites ending at `[J1]`.

The helper validates all fourteen old rewrite steps as data, removes only those two obsolete steps, and rebuilds every new context block using the four retained copy types. The resulting witness has 83 tiles and 167 matrix generators. Exact generic 4×4 multiplication gives the unchanged target in all sixteen entries:

    [[1347733333,37956152,0,0],
     [−57391245432,−1616307011,0,0],
     [0,0,1,2],
     [0,0,0,1]].

The receipt includes the complete twelve-step derivation, each tile block, the entire tile sequence and generator word, and the final product. It also checks the full correspondence word equation, not merely the lower matrix block.

Independent local checks reconstruct all 87 transition rules from the pinned JSON table and compare them to the actual original rules. For all binary left/right contexts of lengths zero through two, the checker inspects 1,470 live configurations, including 49 halting contexts. A direct tape-list transition formula checks every nonhalting next word and rejects premature cleanup. It also verifies cleanup to `[J1]` for all 49 binary context pairs and checks terminal irreducibility. These bounded fixtures corroborate the general invariant proof; they do not decide nonhalting or replace the published universal-source theorem.

The entry point is a bounded, reproducible CLI, not a newly hardened general-purpose compiler API. It verifies the ZIP and every selected member before using data, makes every check explicit rather than relying on Python assertions, and compares saved receipts with exact JSON types. All original files remain unchanged.

    python3 /absolute/path/group_directed_semigroup193.py --repo-root /absolute/path/Proofs --expect /absolute/path/group_directed_semigroup193.json

Writer and fresh saved-receipt replays from `/`, normally and under `python3 -O`, passed. No archived executable or historical suite was run.
