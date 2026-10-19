# Independent review: MP-first falsity, variants A and B

Review date: 2026-10-18. Source pin: `7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.
Reviewed document: `../logical_routes/mp_first_f_proof.md`, SHA-256
`edff65722d0105d85bb387099051c7b0bb20519e21b2b5ac595570b21889f8fc`.

## Verdict

**The ordinary proof is sound for its stated abstract command semantics.** In
particular Variant B may clear D after successful MP, omit the dummy zero push,
and replace NIP by unconditional POP. Its independently proved derivation-block
compiler and fair scheduler yield

`VariantBHalt(s) iff C254(1)` for every initial state satisfying the stated
numerical theorem-stream invariant. It therefore retains the established
ordinary ZFC calibration at the specified seed. This conclusion does not need
a PA result or a new Lean proof. No exact binary implementation or state saving
follows from the abstract theorem alone.

The document now correctly rejects the original direct `147 -> 170` edit. The
corrected helper diagnostics pass, but remain finite tests. None of the reviewed
artifacts is a new verified sub-246 machine.

## Checked mathematical obligations

The review compared the document against `Code254.lean`, `Enum254.lean`, and
`EnumSafeStart254.lean`, including the actual C254 constructors, AX stack order,
command packing, scheduler draining, and padding lemma.

1. **Relative falsity and arbitrary numerical codes.** F is exactly code 1,
   not an external primitive false symbol. The invariant is C254(T), Good(S),
   C254(H), with unrestricted D. Every rho row and the gate's bundle alternative
   has outer implication, hence value divisible by 4; the ninth row is U(a,H),
   hence congruent to 2 modulo 4. The other gate alternative is 0. These facts
   hold for all numbers, including malformed formula codes and parameters 0
   and 1. The occurrence of 1 inside a relative-negation expression is not a
   theorem-stream entry. C254.truth explicitly supplies 0, including the alias
   I(0,0)=0. No induction on decoded formulas is used.
2. **First-F argument.** Original DROP, nonhalting NIP, AX and failed MP preserve
   F-freeness; successful MP does so exactly when its target differs from 1.
   Thus original halting from an F-free state has an earlier MP-to-1. Variant A
   agrees until that first MP. The reverse implication uses native completeness,
   not the false assertion that the same old candidate must halt after creating
   1. Soundness is necessary for this reverse implication from arbitrary starts.
3. **Variant B soundness.** Failed MP resets T,H to truth. Successful MP derives
   its target by the native MP rule; clearing D and leaving S unchanged do not
   affect the invariant. Unconditional POP merely exposes an already-good
   stream member. Halt implies C254(1), without F-freeness.
4. **Strong block contract.** For each finite C254 derivation of X, the displayed
   block works for every numerical T,S from (T,S,0,0): it either halts or returns
   (X,S,0,0), and X=1 forces halt. Early halt in a recursive subblock is allowed.
   This is essential when intermediate proofs themselves derive 1; no hidden
   consistency assumption is used.
5. **Exact stack counts.** AX pushes ten entries: eight rho rows, U(a,old H), and
   old T. In discard, MP 1 must fail because I(T,1)>0 while H=0; AX then uses
   a=c=1 and pushes old T=0. Ten POPs restore S and H=0. Selecting rho_j consumes
   j entries; DROP adds the gate; `11-j` further POPs consume that gate and the
   original `10-j` remainder. The last removed entry is old T=0. Bundle selection
   uses ten POPs. GEN places X in H, uses a=c=i to force gate=0, selects row nine,
   then removes exactly the pushed gate and old T by two POPs. All counts hold
   even for numerical S=0 or zero-valued entries: inverse-pairing identities,
   rather than physical list lengths, are the relevant equations.
6. **MP composition.** The six pre-final states in the document are correct.
   Immediately before `MP B`, D=0, T=A, H=I(A,B), and the original S is restored.
   Consequently it halts if B=1 and otherwise returns (B,S,0,0). No cleanup or
   dummy stream entry is needed. Truth, MP, GEN, all eight rows, and gated bundle
   exhaust the actual native constructors. Both bundle inequalities are retained.
7. **Fairness and arbitrary starts.** Every nonhalting abstract command is total
   on natural-number registers. When pl>0, decoding first uses pl-1 and sets the
   next list pointer to a nested Cantor component, hence at most pl-1. Thus an
   arbitrary internal list pointer drains in finitely many commands unless halt
   occurs. At a boundary np increases exactly once, so all N>=initial np are
   eventually attempted unless an earlier halt occurs. These assertions do not
   require theorem soundness of working registers.
8. **Tail padding.** Prefixing the contradiction block by `AX 0 1 1 u` resets
   D=H=0 from every working state. The produced T,S may be arbitrary, which is
   precisely what the strong block contract permits. The unchanged packing is
   `P(3,P(1,P(1,P(u,tail))))`; nested component inequalities give N>=u. Choosing
   u>=initial np places this halting candidate in the enumerated tail. Hence
   C254(1) implies halt even from an unsound six-register start. Soundness plus
   this implication gives the advertised iff on sound starts.

## Reusable transfer statement

Let E_B be exactly Variant B with the original numerical scheduler. Let M be a
finite binary TM, and let s be a sound six-register state. Suppose ZFC proves:

- the finite blank-tape startup of M reaches a certified encoding of s;
- every simulated command/scheduler step is a finite, strictly positive machine
  segment with the stated full-tape/head exit and preserved representation;
- machine halting occurs exactly at E_B's halt (with coverage of every reachable
  nonhalt entry, so malformed or missing cases cannot introduce another halt or
  permanent internal loop).

Then ZFC proves `BlankHalt(M) iff C254(1)`. The proof is finite positive-segment
simulation in both directions, followed by the theorem above. Combining the
already reviewed ordinary native calibration `C254(1) iff not Con(ZFC)` yields
`not BlankHalt(M) iff Con(ZFC)`. Nothing here proves Con(ZFC); it proves an
internal equivalence. The required proof-theoretic endpoint is ZFC. The
finitary nature of the abstract argument supports local mechanization, but this
review does not certify the document's optional PA formalization claim.

## Concrete implementation boundary

Original NIP's equality test cleared incoming H as a side effect. Helper 170
pops additively into H, so `147.right=170` computes old H + head(S), not head(S).
The corrected route is a sequential clear/pop node `(199,170)`, where 199
clears H. A proof of the literal implementation must additionally establish:

- exact entry conditions for 147, 150, 198, 199, 132 and the new composition
  nodes; which scratch registers are zero, and who ensures that condition;
- total termination and full register effects for all natural inputs, including
  H=1, D=0/1, zero streams and nonzero scratch cases actually reachable;
- preservation or a replacement of dirty-scratch absorption for the changed
  source. The old theorem is about the old source and cannot be silently reused;
- complete source-graph/table simulation, actual initial tape and bootstrap, and
  a count of every live working state, return adaptor, selector, and initializer.

Fresh re-execution of the corrected existing diagnostics, with only its result
sink redirected to this review directory, passed 48 goal-copy cases, 490 MP
cases, and 936 corrected POP cases. Files: `mp_first_corrected_fresh.json` and
`.log`. Script SHA-256:
`1daff2d2923c43e0e06cefda8dd864256c68afc0aa51d744b068227a283bbd73`.
Assertions were enabled. This replay is useful regression evidence, not a new
unbounded helper proof. The inspected corrected compressed experiment reports
269 working states, 538 rows, and `calibration_proved=false`; it supplies no
sub-246 solution. Its results JSON SHA-256 is
`1cc92becc0983229fdc38813aea3d11abcd3a328275109bb8192fa4d69983779`.

No shared checkout or other worker artifact was modified. No Lean build,
external repository write, or new software installation was performed.
