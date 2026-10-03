# Independent review of the two-cone recoder transfer

**PASS; no correction requested.** I read the complete frozen [source](native_binary_recoder_factored128.py), [receipt](native_binary_recoder_factored128.json), and [proof note](native_binary_recoder_factored128.md). This is a bounded delta audit against the complete authenticated inline130 and exact-width Grill receipts. It does not rerun the long historical native builder, the prior compiler suites, or the accepted exact-width semantic proof.

The independent [checker](review_native_binary_recoder_factored128.py) and [receipt](review_native_binary_recoder_factored128.json) pin all three author files and the eight source dependencies. They independently select the actual original full sources, reconstruct the generic-width power chains, validate each changed cone, and check complete source/finalizer conservation.

## Exact local and complete identities

Both native recoder cones literally compute `UM=wn2*sn2` and `ksn2=k*sn2`. Their k values are supplied positive auxiliaries. The retained comparison with the distinct register R10b cannot be used off-zero. In the inline/generic recoders the prefixes are `geo__` and `and__`; in the complete Grill source they are `rec__geo__` and `rec__and__`.

For independent X,Y,k and E=XY, V=kY, the old coefficient and replacement have the same exact expansion:

```
(E²+X)V² = X²k²Y⁴+Xk²Y² = (EV)(EV+k).
```

Each old four-gate cone3M+1A becomes three gates2M+1A. In each occurrence the three removed intermediates have precisely their declared private consumers and are absent from all comparison operands and the entire finalizer tail. The comparison output L9 retains its name and value; its original R9 convention is unchanged.

The independent script reconstructs the expected replacement rows and confirms that **every other complete source row is identical**. It proves each actual cone by coefficient expansion and then uses two distinct established L9 cuts to check every common downstream register, every residual and the entire final polynomial. The two cuts are distinguished by name, so no accidental identification of the two coefficient values can justify a false downstream identity. Coordinates, comparison lists, domains and semantic metadata are unchanged.

The exact-width history contains its already translated `hist__and__first_unit`. It contains no old history L9 coefficient cone. The history unit factor is therefore untouched, and there is no third saving.

## Fully paid counts and preserved scope

| Form | New comparison M+A | Comparisons | Positive auxiliaries | New polynomial M+A | Complete polynomial total |
|---|---:|---:|---:|---:|---:|
| Inline width4 |65+63|34|49|99+130|229|
| Generic width32 |68+63|34|49|102+130|232|
| Generic width784 |74+63|34|49|108+130|238|
| Exact-width Grill |4946+11200|48|3217|4994+11295|16289|

Every total loses exactly two multiplications from its parent, with the addition count unchanged. The independent checker recounts all16 old/new comparison and polynomial ledgers, verifies every paid gate is live, and checks the complete set of free coordinates. The standalone width4 comparison bound is128, and the generic formula is126+mu(b), where the explicit power chain has mu(b)=floor(log2(b))+popcount(b)−1 products. The executable exposes only the four advertised selected variants.

The generic chain changes only the original two private q^4 gates and the fixed scale coefficient. Its exponent accumulation and fixed coefficient are independently checked against the actual emitted rows. Both native kernels and all34 comparisons remain. The supplied input and spread output stay outside the49 auxiliaries.

The stated exact standalone degrees40,66,1570 agree with the actual formal bounds and the unchanged-parent leading-term proof. For b+1>20 the repunit residuals have nonzero degree b+1 top forms; otherwise the first AND norm supplies degree20. Squared residuals cannot cancel their leading forms. The full Grill degree283247 remains an **upper bound only**, which the source metadata and note correctly retain.

In the complete Grill packet, only ordinary positive x is supplied; its3,217 positive witnesses include the encoded queue value and spread output. The following conditions and their paid rows are all unchanged: binary(x+1) in least-significant-first order, canonical source-bit length, denominator-cleared E-value, exact native width, and retained positive width slack. The finalizer tail is literally the old `U*(1+S_H+S_L)-1`, with all loader residuals inside the sum. Thus the prior soundness and positive converse transfer through a same-coordinate polynomial identity.

The1,568-phase measured table remains the nonuniversal reject-all example. No new universal table, input recognizer or arithmetic upper bound for a universal equation is claimed. The205-operation program011 example remains distinct. There is no newly fixed external computation horizon.

## Review evidence and limits

Independent checks passed eight full local coefficient identities,24 private-consumer checks,20,343 shared-register DAG identities,150 residual identities and four whole-polynomial identities. Twelve bounded complete numeric cases include signed and rational assignments. For the long Grill source, selector hats are held at1, so these are off-zero algebra fixtures, not accepting histories or materialized Pell extensions.

I also checked the documented canonical API boundary and four concrete altered-packet rejections, including substituted R10b and a corrupted full finalizer. The source reconstructs fresh packets, validates complete typed parents/children, reauthenticates dependency bytes and imports no historical compiler. This review does not claim an exhaustive hostile-caller audit; the receipt's broader author guard tests are separate evidence.

The complete author proof note and its interface/count claims are consistent with the actual sources. No repository or frozen parent file was modified. The author's proof note is pinned, so reviewer provenance remains in this separate packet.

Fresh read-only replay matched the full saved receipt:

```sh
python3 review_native_binary_recoder_factored128.py \
  --root /path/to/native-stream-queue \
  --subject-root /path/to/native-stream-queue \
  --expect /path/to/review_native_binary_recoder_factored128.json
```

The checker uses only the Python3 standard library and does not execute the author verification suite.
