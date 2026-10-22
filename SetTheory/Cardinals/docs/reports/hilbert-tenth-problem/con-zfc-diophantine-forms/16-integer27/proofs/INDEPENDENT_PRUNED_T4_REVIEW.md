# Independent review of the 5,268-tile pruned T4 compiler

Reviewed against the pinned `11-t4/bridge/BRIDGE_AUDIT.md`, its `check_t4.py`, and the new `../compiler/pruned_t4_check.py`, tile list, specification, and support receipt. The review covers unbounded semantic preservation and the finite layout formulas, not merely control-run tests.

## 1. Local enumeration

The new predicate is a conjunction of the old T4 predicate and three stronger restrictions. Therefore any globally valid new plane is globally valid in the old T4 language. The old marked-plane-to-blank-halt soundness theorem transfers without alteration.

The new enumerator is exhaustive, despite not iterating all 439 successors explicitly. For a V center the only candidate successor is V; for H the only candidates are L,Q,R; for every other center, a successor is either H or the uniquely determined ordinary deterministic successor. A next V would violate V propagation, and a next phase would require an H predecessor. Thus its `next_candidates` branch split loses no old or new tile. The one-head census contains exactly `433*6^2+6*(6^2+2*433*6)=46980` triples.

## 2. Every finite blank halt has a pruned canonical helix

Take a genuine finite blank halting computation. Include the position reached on the transition entering halt, and then complete the halting state by its stationary self-loop. Choose two tape positions at either end lying strictly outside every head position visited at any time. These positions remain blank and headless throughout the computation: a Turing machine writes only at the head position. Additional margins may be added arbitrarily.

In a finite rectangle, place a V column, one H row, one initialization row L...L,Q,R...R, the genuine run, and arbitrarily many repeated halted rows. Each of the first and last two ordinary interior positions is permanently blank/headless. Width and height remain independently selectable as sufficiently large powers of five.

Now use the same helical extension as the inherited T4 proof. All newly imposed clauses hold at every integer point:

* An edge not touching V remains in one rectangular row. It is H/H, one of LL,LQ,QR,RR, or ordinary/ordinary, exactly the allowed non-V cases of `edge_valid`.
* An edge touching V has an adjacent interior endpoint that is 0 in an ordinary row, L or R at the appropriate end of the initialization row, or H in the boundary row. The two sides of V may belong to consecutive time slices because of the helix; the allowed endpoint choices are independent and therefore still hold.
* An ordinary center next to V is the first or last permanently blank margin cell. Its other neighbor is the second permanently blank margin cell, so the new head-exclusion clause holds. No assumption that two sides of V have the same time coordinate is used.
* If the next-time center is H, the center lies in the final halted row. Any head among its same-strip neighbors is in state215; any neighbor across V is headless. This proves the stronger next-H head restriction.

These checks cover the ordinary transitions, phase-to-ordinary transition, ordinary-to-H closing transition, H-to-phase opening transition, V columns, and the helical one-row seam. They are not confined to the two finite control machines. The inherited exact overlaps and unique canonical Start are unchanged.

The new forbidden selector `(V,H,V,Q)` passes the centered local predicate, but cannot appear in a globally valid plane: its neighboring V columns persist, so the next Q would have a V neighbor on both sides. The phase endpoint rules would require it to equal L and R, a contradiction. Forbidding it therefore removes no canonical or other globally valid marked plane.

## 3. Actual layout and masks

With k=5268 and alphabet size439, the formulas give ell=13,p=1083,jmax=2843,m=7029, and two free dummy positions. The support cardinality is

    5268 + 4*439 + 2 + 4 = 7030 = m+1.

The positions, both clause bands, and all 1319 copy/anchor targets use the same generic T4 layout equations. The independently inspected support audit verifies their actual instance, including absence of field collisions and both rotation tests.

The second low dummy position does not introduce a second upper dummy bit. The low mask subtracts one low bit at every allowed position other than selector1, plus exactly one additional upper bit at the first dummy. Thus its population is d-7030. A nonaligned radix rotation still has at most one possible odd spill position. Here that spill position coincides with the second ordinary low dummy position; its ordinary low bit rotates to an even digit, so the parity argument remains unchanged.

The clause mask has `pc(mu)=13-1+2843=2855`, giving

    pc(MF_native)=2*2855 + 3*439 + 2 + 1 = 7030.

The fixed radix exponent b=78125 exceeds both the mask and carry thresholds; the receipt's exact finite mass calculation needs only22909 bits. The cell length is9765625, with support maximum320085 and band positions1246533,1886707. The band gap640174 exceeds twice the support maximum and is2 modulo4. The opposite circular gap also exceeds the support span. Consequently the inherited carry, uncontaminated-band, binary alignment, and whole-cell alignment proofs retain their hypotheses.

The arithmetic instance must use all four newly specified ports together, including `MF_source=MF_native+B-1`. Changing the forbidden tile changes the selector order and hence DC; this is correctly part of the new complete recipe.

## 4. Canonical parity and actual-index tuning

The paired clause contributions cancel modulo five because the radix exponent b is odd and the band gap is2 modulo4. The unchanged bare-shift formulas give `2DC-DR=3 mod5`. Therefore the inherited adjustment of the actual packed rank by dummy bits remains available. Such dummy changes preserve the selected local windows and cannot violate any new pruning clause.

The new d=b*L is5^17, an odd integer. Independently padded width and height can both be powers of five, so the canonical word length N is odd. The unchanged mask congruences `MC=2 mod4` and `MF_native=4 mod8` preserve the final canonical rank R=3 mod4. Hence the normalized canonical scale `w=2^(R-dN)` is an integer square. The odd-i specialization and odd auxiliary y from package14 consequently transfer to this complete coefficient tuple. This is the extra completeness property needed by the27-integer construction; existential compiler equivalence alone would not have justified that transfer.

## Conclusion

No new semantic or coefficient-interface gap was found in this adapter. The5,268-tile language and base `B=2^(5^17)` can be used as a whole tuple for both the improved positive13 polynomial and the27-integer polynomial, relying on the same inherited unbounded T4/native/Pell compiler theorems. The bounded checks support the finite data; the arguments above supply the unbounded padding and seam preservation.
