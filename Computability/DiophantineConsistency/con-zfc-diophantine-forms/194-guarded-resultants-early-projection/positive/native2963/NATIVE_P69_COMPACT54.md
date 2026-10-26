# P69 with the complete compact54 tuple

The ordinary mathematical argument covers the fifteen-positive-variable
P69 equation with the **whole** compact54 tuple. Its required chain is:

1. `ShortCircuit.value_zero_iff_baselineValue_zero` proves that the literal
   P69 and P67 evaluations have the same zeros at the same positive
   coordinates, for every positive beta. This is a checked local Lean theorem.
2. Package36's `proofs/INHERITED_P67_PROOF.md`, sections1–6, gives P67's
   ordinary soundness and completeness for the native coefficient interface.
   It is parameterized by the interface, rather than its then-selected
   beta value. Sections2–4 retain the exceptional weak transport case until
   the index signs are recovered; they do not assume C>0 prematurely.
3. Package36's `proofs/INHERITED_PELL_AUDIT.md`, sections6.1–6.4, supplies
   fresh Pell witnesses at the **actual tuned rank**. In section6.3 the
   normalized multiplier is explicitly `psi_A(2cR)/c^2`; its integrality
   is proved. No arbitrary ordinary multiplier is divided by Delta.
4. `candidates/split116-compact/compact54-sharp/provenance/interface_proof.md`,
   sections3–6, supplies the complete compact54 native interface, cofinal
   independently padded odd cell counts and the actual-rank controller.
   Its section6 explicitly permits replacing all four ports of a skeleton
   whose correctness theorem uses this interface. Its ordinary marked-Wang
   interpretation composes with the inherited K215/refutation calibration.

The compact54 source pin is `4b4349064a750ba6347293b55874a7f92abdd0db`.
Its radix parameters are `rho=2^89`, `L=4831`, `B=rho^L=2^429959`.
The ports must be exactly

```
beta=B−1, K0=DC+B*DR, MC, MF=MF_native+B−1.
```

The last shift occurs **once**. In particular P69's positive z is the
original transport coordinate:

```
Nt=(K0+w)C+(q−F)−z(q−1)=1
iff (K0+w)C=F+(z−1)(q−1).
```

The coordinate z−1 may be zero. Replacing it by report52's strictly positive
shifted quotient would change the generic positive-domain zero set and
would need a separate completeness argument. The P69 composition makes
no such replacement.

Consequently it is accurate to describe the completed ordinary argument
as an equivalence of positive unsolvability and Con(ZFC), while explicitly
stating that the end-to-end Lean native calibration and the derivation in
the encoded object-language ZFC calculus remain open. The local P69/P67
Lean equivalence is not itself an internal-ZFC reflection theorem.

The one-page coefficient action seed has a separate finite checked binding
in `NativePackedMachine54.lean`. Its literal 1294-decimal-digit numeral has
4298 bits and encodes all430 dense actions by

```
digit(j) = (seed / 1024^j) % 1024,
next = digit(j)%256,
write = (digit(j)/256)%2,
moveRight = digit(j)/512,
currentState=j/2, readBit=j%2.
```

The decoded215-row list and resulting machine are definitionally equal
to `KDense215.rows215` and `KDense215.machine215`; the blank-halting
predicates are therefore also definitionally equal. All three proofs use
`rfl`. The row equality has no axioms; the machine equality uses `propext`,
and the blank-halting equivalence uses `propext` and `Quot.sound` through
the imported machine/run definitions. The numeral matches `candidates/one-page/COMPACT54_SEED.txt`,
SHA256 `5e745601d22ee2cce780db7bac7323ecb7141692c27852fce992f85758d2afab`.
An independent comparison also matches all430 exported JSON actions to
the current Lean dense table. This is the dense215 table, not the distinct
K230-label representation in `KTable215`.

This finite machine binding does not prove that the mode/coefficient
recipes decode to its runs. That native/Wang implication, its converse,
and the internal ZFC biconditional remain separate semantic obligations.
