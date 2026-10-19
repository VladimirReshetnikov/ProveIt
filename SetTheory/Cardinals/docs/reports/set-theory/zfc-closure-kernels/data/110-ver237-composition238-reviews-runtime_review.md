# Independent mathematical review of the direct runtime checker

## Finding

The reviewed symbolic rules support the claimed universal instruction interface on the supplied binary table. I found no mathematical defect in the rules, tape representation, finite-list abstraction, halting checks, or source-path normalization. This is an ordinary mathematical review of executable proof construction. It is not a Lean/Rocq kernel replay.

The review covers `validation/symbolic_runtime.py`, `validation/independent_runtime.py`, `validation/check_literal_runtime.py`, `formalism/extra/check_rotation_certificate.py`, the accompanying source-equivalence argument in `formalism/source_result.tex`, and the pinned definitions in `semantic_interface/RegisterPath.lean` from the incoming boundary239 archive. The direct runtime receipt must still be checked for the exact composed238 table and final boundary source; a receipt for a preceding table does not suffice.

## What the quantified statement means

For every leaf of the final 6,455-leaf source, and for each of the two decrement guards, the checker starts at inherited dispatcher96 with:

- nine independently arbitrary natural register values, subject only to the selected decrement guard;
- arbitrary natural additional header gap;
- an arbitrary natural first spare value;
- an arbitrary finite remaining spare list, possibly empty;
- the exact binary instruction path and the all-zero tape exterior.

It proves either an exact finite transition block to the specified successor frame, or entry into the separate halt outcome254 for a literal halt instruction. A nonempty spare list is part of the representation: the explicit first spare ensures that premise, the finite bootstrap supplies167 spare blocks, and increments append a value-one block while other instructions preserve the spare list. No bound on natural register values, gap, or spare-list length is introduced by the finite number of symbolic rules.

The 4,000-iteration limit bounds proof construction. A successful case contains unary and finite-list induction rules, so its actual concrete duration can be arbitrarily large. An exhausted construction bound fails to prove a case; it cannot create a pass.

## Tape representation and literal steps

The two atom lists describe the tape immediately on either side of a cut. Each list runs from the cut outward. `direction` identifies which adjacent cell is scanned. If a transition continues in the current direction, the written cell moves to the opposite list. If it reverses direction, the written cell remains on the source side and the scanned side switches. This agrees with an ordinary binary single-tape transition moving one position left or right.

`motion` independently records the signed change in head position. Comparing normalized tape shapes and final direction identifies the relative tape; the additional exact motion check fixes its absolute translation. Thus the interface is not merely tape equality up to an uncontrolled shift. For nonhalting source instructions the required motion is exactly minus the carry-overflow indicator.

Each run length is an integer affine expression in thirteen variables: a constant, gap, nine registers, the first spare, and total width of the remaining spare list. Coefficientwise nonnegativity is a sufficient condition for a universally nonnegative length; requiring it can reject a true identity but cannot accept a negative length. One literal step may consume a run only when its constant coefficient is at least one. This makes that scan valid for every assignment of the natural parameters.

## Unary and finite-list induction

A unary macro applies only to a literal self-loop that moves in the current scan direction. Iterating that exact transition through a same-symbol run of length n takes n transitions, writes the stated symbol throughout, and moves n cells. The n=0 instance is the identity and is valid even when a symbolic run evaluates to empty. The main proof still requires a positive constant term in its total duration.

The four list traversal schemas use entry states73,95,48,112. Each is reconstructed from the supplied literal table using only literal transitions and unary self-loop induction. The one-block proof starts and finishes against opaque left/right contexts, which cannot be read. It returns to the same entry state, with the intended orientation, after exactly v+2 steps for an arbitrary natural block value v. Structural induction on a finite list therefore justifies their use on any list of blocks. The empty-list case contributes zero steps and moves no cell.

The list width variable is interpreted as the actual sum of v+2 over that list. Treating its affine contribution as an arbitrary nonnegative variable is conservative: both block families have exactly that width, and a conversion between them does not alter the list's values or order.

Writing B(v)=0 1^(v+1) and C(v)=1 0 1^v, the normalization identity is

    C(A) 1 = 1 B(A).

For the empty list both sides are the single bit1. If it holds for A, then

    C(v :: A) 1 = 1 0 1^v C(A) 1
                = 1 0 1^(v+1) B(A)
                = 1 B(v :: A).

Reversing the complete word gives the second rule

    1 reverse(C(A)) = reverse(B(A)) 1.

These are exact finite-word identities, including arbitrary zero-valued entries. They justify both orientations implemented in `normal`. Adjacent same-symbol runs may be concatenated, and an infinite zero exterior may absorb an adjacent finite zero run. None of these equalities hides a tape cell or changes head position.

## Halting and positive progress

The designated halt outcome254 has no outgoing rows. It cannot be hidden by a successful unary macro, whose transition returns to its nonhalt entry state. It also cannot be hidden by a list schema: the schema is proved from literal transitions and self-loops, must finish at its nonhalt entry state, and would fail on any attempted outgoing transition from254. No list rule is used while deriving a one-block schema.

For a nonhalt source instruction, reaching254 before the required frame causes the next symbolic transition lookup to fail. For a halt instruction, the checker accepts entry into254 directly. Every successful instruction case has a coefficientwise nonnegative affine duration with a strictly positive constant term. Consequently successive source instructions correspond to positive finite binary blocks. This supplies the needed progress condition for both finite halting runs and infinite runs.

There is no requirement that the symbolic block stop at the first incidental occurrence of dispatcher96; an instruction theorem may use a longer positive block. This is sound because the theorem is an existential exact finite transition statement, the tape and control at its specified endpoint are checked, and an intermediate halt cannot be traversed.

## Source paths and composition between instructions

The source semantics in `RegisterPath.lean` reads a finite path with trailing zeros, finds a leaf, and uses the consumed leaf path (zero-extended or truncated to its depth) for instruction arithmetic. The Python helpers implement the same fixed-length increment, zero-counting break, and one-counting continue. Their explicit carry bit does not change the source operation; it accounts for physical motion of the binary representation.

The source-control checker proves the finite tree is complete and prefix-free. Its `locate` follows the path with zero padding and rejects any generated successor with a discarded nonzero suffix. Together with the initial empty path, this establishes the exact identity

    P 0^omega = p_loc(P) 0^omega

for every reachable successor word. That identity is the necessary bridge between a binary successor frame whose stored word may be short or have trailing zeros, and the next runtime case expressed with the full encountered leaf path. Changing to the full leaf path leaves the represented tape unchanged because the fixed header budget depends on 64 minus the path length. All source leaf depths are at most48 for the boundary source, so this budget is nonnegative for every allowed gap.

The graph certificate checks both decrement outcomes and every control successor for every leaf. Equality of these finite descriptors, together with identical register actions, gives a direct strong bisimulation of the two source programs from the empty path. This does not rely on informal associativity of source syntax.

## Items that must accompany the final claim

1. **Exact source identity and source certificate.** `check_literal_runtime.py` pins the boundary source bytes by SHA256; it does not call the baseline-specific `validate_inputs`. The final package must retain the independent full-tree/control certificate and the static extraction connecting the original source to the pinned calibrated Lean definitions. The source certificate already supplies the required tree and successor canonicality facts.
2. **Exact blank initialization.** The universal instruction interface begins at dispatcher96. A separately checked exact blank prefix must identify the initial path, physical/logical register mapping, nonempty spare list, and header gap for composed238. A long run without that exact complete-frame equality would not fill this obligation.
3. **Exact table binding.** Retain the full literal table, canonical relabeling proof, source and table hashes, and a fresh complete composed238 runtime receipt. The proof is specific to those transitions and that source.
4. **Ordinary proof versus kernel theorem.** The argument above explains the mathematical significance of the finite executable certificates. A new composed238 proof-assistant endpoint is not established by running Python. The inherited calibrated source endpoint remains a distinct input.
5. **Guarded local reduction is a supplementary route.** The separate169-to80 positive-block proof requires the semantic selector guard at old169/read1. That guard must cover the preceding machine's unbounded instruction blocks and its finite bootstrap. A fresh direct composed238 universal runtime plus exact composed238 initialization supplies an independent principal route and does not assume the local-fold guard.

The helper's historical standalone `main`, `clean_dispatch`, and finite fixture runner are not used by the direct universal proof; their fuel limits and heuristic first-dispatch detection do not enter its theorem. The direct proof imports only its table parser, physical register permutation, and exact path-arithmetic helpers.
