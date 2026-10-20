# Seed-G222: second fully checked 222-state candidate

## Exact endpoint

This is an independent 222-working-state, binary, two-way single-tape machine
obtained from the repeated-witness K223 packet (`docs/incoming/` ZIP numbered
`(3)`), not the installed conditional-K223. Initialization is included. Its
canonical state set is 0 through 221, with distinct halt label 222; it starts in
state 0 at the origin of the all-zero tape. All moves are L or R.

The machine tables and source are in `machines/seed/`; verification receipts
are in `evidence/seed/`. The canonical table hash is
`3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476`.
The inherited-K-label table hash is
`726583d188c22ee0d8572083a22497657c60e33fc80159d317767046dbbda365`.
The exact source hash is
`cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e`.

The source has 4,744 primitive occurrences, 208 distinct subtrees including
23 primitive kinds, maximum address depth 36, and maximum zero run 6. The
table has 49 nondecoder engine states, 185 interior source roles, and 12
contextual aliases: 49 + 185 - 12 = 222.

## What changed

The predecessor seed-K223 emits the same restricted equality helper as K224,
but uses the witness request twice in its K core. In exact numeric syntax,
write I, R, Q, E for the four pairing constructors and N(x)=I(x,1). Let

    S = Q(c,I(R(c,a),R(c,b))),
    W = Q(b,I(c,N(Q(b,I(c,N(R(b,c))))))),
    U = Q(a,I(S,W)),
    H = Q(b,I(R(b,c),N(Q(a,I(c,N(U)))))),
    VR = I(R(a,b),Q(c,R(a,b))),
    HR = I(E(a,b),Q(R(a,b),E(a,b))),
    J = Q(c,I(H,N(W))).

The predecessor bundle is N(I(VR,I(HR,J))). The new bundle is N(I(VR,J)).
Both retain the exact gate: c=a or c=b emits the same exceptional value 0.
At the seventh logical row replace

    I(E(c,a),I(E(c,b),E(a,b)))

by

    I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b)))).

This is exactly the G fusion from incoming ZIP `(2)`, composed with the seed
root from incoming ZIP `(3)`. It changes no native deductive theory relative
to the seed predecessor. The seed root's calibration is inherited; it is not
a new claim of equality between seed and conditional formula codes.

## Core-independent logical equivalence

Put d_ab = E(a,b) and kappa(a,b)=R(a,b). The old row is
T: d_ca -> (d_cb -> d_ab), and the extracted old helper is
H_ab: d_ab -> Q_kappa d_ab. Together T and H_ab yield the new row G by a fixed
propositional proof.

Conversely, the retained universal-elimination axiom applied to the consequent
of G yields T. Substituting c=a into G and applying the retained reflexivity
axiom d_aa yields H_ab. The conjunction calculus therefore constructs every
old bundle from the new bundle and H_ab. In the forward direction it extracts
the new bundle from the old one. To obtain H_ab from the old packet at arbitrary
a,b, choose a numerical matrix/private parameter distinct from both endpoints;
the canonical R(a,b)>a,b supplies one. Failed gates emit the same value and need
no transport. These are the same finite native proofs supplied for G223, whose
generic proof uses the K core only as an opaque propositional argument.

Thus the native proof sets agree exactly. Composing with the seed-K223
calibration gives the intended ZFC-provable consistency equivalence. No new
compiled Rocq or Lean endpoint is claimed.

## Independent reconstruction and source binding

`code/construct_seed222.py` performs no search. It checks the frozen predecessor
table, source and grammar hashes; removes the equality-helper macro block and
its composing implication; inserts Rel(a,b), Eq(a,b), All into the seventh
row; and performs one closed right reassociation at source address
1110100100111000. The change to the table has six retained-row edits, two new
states 300 and 301, and deletions of old states 65, 135 and 212. The table
therefore has 223 + 2 - 3 = 222 working states.

`code/check_seed_emitter222.py` imports neither the constructor nor a search program.
It derives both old and new formula words independently from literal ASTs,
checks all 4,744 output primitives, and compares the complete guarded CFG to
a separately associated reference sequence of closed source macros. Nine
all-register finite macro bisimulations tie the actual programs to pinned
Dag230.v and the ProgLib230.v arithmetic contracts. This check covers all
natural a,b,c, arbitrary previous stack/top, and the inherited clean scratch
interface; it does not sample numerical formula codes.

The arithmetic constructor word for the bundle falls from 77 to 65 macro
symbols. The old and new literal source differences are precisely:

- row interval [486,786): +109 primitive occurrences;
- bundle interval [2541,4781): -327 primitive occurrences;
- all other primitive occurrences are identical.

The net 218-primitive reduction gives 4,962 - 218 = 4,744. Both independent CFG
resolvers accept all 6,167 guarded instruction cases.

## Binary runtime and startup

The direct unbounded checker has passed all 6,167 guarded cases of this exact
table and source, using 1,488,390 symbolic rules and all 444 rows. Its minimum
instruction duration is 13 actual transitions. This is the source-runtime
proof, distinct from the finite emitter/decoder checks. Exact blank startup
has passed after 409,835 transitions, reaching the inherited dispatcher at
head -5 with the complete intended frame. Finite traces alone would not prove
the claimed nonhalting equivalence.

## Reproduction inputs

The two new scripts take explicit paths and have no absolute workspace paths.
They use the shared `code/support/` modules prepared for the main conditional-G222
packet. Their three frozen predecessor files are in ZIP `(3)` under
`portable/machine/{sites.json,candidate.k.tm,grammar223.json}`. The candidate
table, source, and canonical map are in `machines/seed/`. Constructor, emitter,
runtime, and bootstrap receipts are in `evidence/seed/` or are regenerated by
the corresponding checks during the complete package replay.
