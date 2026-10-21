# Parity alarm with negative equality: scoped source experiment

## Result and status

The literal source `sites-oddalarm-diseq.json` has **205 distinct subtrees**, **5025 primitive occurrences**, depth47, and maximum zero run6. Its SHA256 is `18d0c453296f464db80fb85540bbc9eb566cebb057606ea8bd89faf2728ead46`. Both source CFG resolvers agree.

The intended formalism interprets raw residue1 atoms as membership and raw residue3 atoms as disequality. Every intended equality constructor `E(a,b)=4P(a,b)+3` is then replaced by `I(E(a,b),1)`. The original exact-one cache alarm is replaced by a four-leaf parity scanner. This is one distinct source subtree smaller than the best current membership-only modulo-four alarm experiment (206), although it is three larger than the accepted 202-subtree source.

**This file does not establish equiconsistency of the changed calculus with ZFC.** The source construction and the scanner contract are explicit; a complete support-aware reverse calibration of the changed equality encoding remains an obligation. No physical machine is allocated or claimed to have 215 states.

## Why parity is a plausible alarm

In a nonempty irreflexive membership model, choose the same object as the value of every variable. Then every membership atom is false and every disequality atom is false. A theorem must be valid under every assignment, so no theorem can be an odd raw atom if the altered calculus is sound for these models. Code1 is still included in the alarm class.

With truth0, implication `I(a,b)=4P(a,b)`, and falsity1 interpreted as self-membership, `I(E(a,b),1)` has the semantics of equality when raw E is disequality. This explains the proposed local constructor change. It does not alone prove the reverse consistency implication for the entire source calculus.

## Exact source edit and scanner proof

The accepted AX primitive stream has six occurrences of its canonical 27-leaf implication constructor followed immediately by three `CI1` leaves. The final increment paths are:

    11010010011101010101101
    1101001001110101011000001
    11010010011101010110000111
    1101001001110101011001001101
    11010010011101010110011100001001111
    110100100111010101100111000111111

At each of these literal tag3 endings the source appends its existing 47-leaf negation constructor, found at `11010010011101010110001111011`. This implements the intended negative-equality constructor at these six sites. The source builder records these sites rather than silently rewriting every raw numeric occurrence of tag3; arbitrary input codes are not recursively normalized.

The scanner is

    (CD5, ((CD5, CC2), CH)).

If H=0, the first decrement exits normally. If H=1, the first decrement succeeds and the second zero branch enters CH. If H>=2, the two decrements consume exactly two and CC2 returns to the first decrement. Induction on floor(H/2) proves termination and the exact contract: halt iff H is odd, otherwise return with H=0 and every other register unchanged. Following it with the accepted NIP pop therefore preserves the old nonhalting NIP effect whenever the scanner returns.

## Why the reverse calibration cannot be asserted from a tag relabel

The falsity constant1 is syntactically the membership atom `Rel(0,0)`. Therefore the numerical equality representation `I(E(a,b),1)` contains variable0 even when a and b differ from0. Semantically that extra occurrence is uniformly false in an irreflexive model, but the repository's bundle calibration also tracks syntactic support, atomic vacuity, literal encodings, and the numerical coupling between the formula parameter c and a fresh binder named c. A recursive raw-code translation does not automatically preserve those side conditions or exact bundle identities.

A promising repair is to change the abstract formula encoder itself: keep equality as an abstract primitive and encode it with this negative raw atom. Its numerical code still dominates every free variable index, and the equality-vacuity axiom can be emitted for the abstract atom even though its raw implementation contains a syntactically extra false witness. To complete this route one must reprove the logical embedding and the encodable-bundle/ZFC comparison for that encoder, including binder freshness and the use of all raw junk codes in soundness. Those proofs were not supplied here.

The result is consequently an explicit state-priced **source** research lead, with its precise remaining calibration obligation, rather than a claimed consistency machine.
