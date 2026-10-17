# Checked coordinate, Cantor-order and prefix-stack modules

## Files and verification

All four delivered modules compile with
Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The complete captured compiler output is in `../evidence/lean_verification.json`.
All reported theorem dependencies are subsets of Lean's usual
`propext`, `Classical.choice`, and `Quot.sound`; there are no new axioms,
admissions, `sorry`s, or external decision oracles.

The exact source definitions are reproduced from the ProveIt research
archive `zfc_consistency_research_2026-10-16`, specifically
`formal/src/FirstOrder/Fol.lean` and
`formal/src/BusyBeaver/ZFC/Enum254.lean`. The short proof of Cantor
injectivity is adapted from the former, with attribution in the module.
The files import only `Std`, so they do not require the remainder of that
development to check.

## What the Lean modules prove

The two coordinate modules check that NAND has no fixed point and that
the diagonal update construction yields an injective sequence of distinct
ground coordinate names. `FiniteKernelSelectors.lean` uses the original
term q=N(o,o). `FiniteKernelSelectorsIndependent.lean` uses a separately
given q with q≠o, matching the 901-bit kernel. They prove the coordinate
construction, not the entire finite-theory consistency calibration.

The Cantor module uses the literal conventions

    tri(0) = 0; tri(n+1) = tri(n) + n + 1
    P(x,y) = y + tri(x+y)
    pack(DROP x,r) = P(1,P(x,r))
    pack(NIP x,r) = P(2,P(x,r))

and the exact MP/AX alternatives and `encL` continuation convention.
An empty continuation is 0; a nonempty continuation is its candidate code
plus 1. It checks the following results:

* `P_left_strict` and `P_right_strict`: strict monotonicity in each input.
* `pack_strict`: strict monotonicity in the continuation for every command.
* `encL_injective`: distinct nonempty command lists have distinct codes.
  The empty list is intentionally excluded: singleton MP0 has code 0.
* `marked_occurrence_lower`: replacing a NIP by DROP at any marked position,
  while preserving the parameter and all other commands, strictly lowers
  the numerical code of the whole candidate.
* `occurrence_image_injective`: two images cannot agree both in candidate
  code and in marked position unless the original marked occurrences agree.
  The inverse is the same local opcode swap. Keeping the position is
  essential; the map is an injection on occurrences, not just candidates.

The stack module takes the resulting earlier-push injection as an explicit
argument. It proves, for every prefix of a total event stream,

    number of NIPs in the prefix <= number of DROPs in the prefix,

and the stronger fact that immediately before a NIP at position n,

    number of earlier NIPs + 1 <= number of earlier DROPs.

This last inequality is `before_pop`. It includes the current pop in the
domain of the injection and only strictly earlier pushes in its image.
`bottom_unread` then checks that any witnessed good prefix with at least
this remaining credit protects an arbitrary initial bottom object from
the next pop. The only stack representation assumptions are

    head(push(a,s)) = a; tail(push(a,s)) = s.

No uniqueness of a finite-list encoding is required. In particular the
fact that P(0,0)=0 does not invalidate the witnessed-prefix argument.

## Ordinary integration with the enumerator

The remaining connection to `Enum254` is a short mathematical argument,
not a new full Lean theorem in these two modules:

1. Decode each candidate number to its unique nonempty command list and
   concatenate these lists in increasing candidate order. This is a total
   syntactic event stream. The actual execution follows a prefix of it until
   its first halting NIP, if one occurs. This definition works even in the
   halting case and does not assume an infinite runtime.
2. Replace each marked NIP by DROP and retain the marked position. The
   checked code-order theorem puts its image in a strictly earlier
   candidate, and checked occurrence injectivity prevents collisions.
   All commands of each earlier candidate occur before the current command.
   Thus the hypotheses of `EarlierInjection` hold for this event stream.
3. Start with PL=NP=D=H=0 and arbitrary TW and WS. The first candidate is
   singleton MP0. In both branches it sets TW=D=H=0. A successful branch
   additionally pushes 0; a failed branch leaves WS unchanged. It is
   incorrect to say this MP must fail: `wim(0,0)=0`, so TW=0 succeeds.
4. After this first step, maintain a finite list of theorem-valued entries
   pushed above the arbitrary initial WS. DROP adds one entry, AX adds ten,
   and successful MP adds one. Only NIP removes an entry. The prefix length
   is consequently at least the number of completed DROPs minus the number
   of completed NIPs. The current-pop inequality guarantees a nonempty
   witnessed prefix at every successful NIP.
5. The existing calculus-preservation cases for MP, DROP and AX show that
   TW, H, and every newly pushed entry remain theorem-valued. The protected
   pop theorem gives the NIP case even though the original bottom of WS may
   contain falsity or other non-theorems. If NIP halts because H=1, H was
   already theorem-valued before this attempted pop, so the calculus proves
   falsity. No reading of the arbitrary initial bottom is involved.
6. Completeness uses the existing universal halting command block and the
   existing candidate-reach/drain argument, generalized to this starting
   state. Neither requires the initial stack to be clean.

The resulting ordinary theorem is that the exact enumerator started from
`(PL,NP,TW,WS,D,H)=(0,0,t,w,0,0)` halts if and only if its calculus derives
falsity, for every natural t and w. Applying this to a 252-state machine
also requires the separately checked exact startup trace, literal
register-machine refinement, physical tape simulation, and calculus/ZFC
calibration. These two Lean modules do not claim to formalize that entire
endpoint.
