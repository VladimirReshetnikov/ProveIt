# Two fewer additions in the complete controller-flow equation

The complete actual matrix source costs **1,677=801M+876A operations**, with the same **146 positive witnesses**, twenty residuals and exact degree **35,587** as the frozen1,679 source. The diagnostic improves303 to **301=126M+175A**, keeping51 witnesses and degree1,363. This is an exact identity on every supplied tuple, with no change of coordinates or accepted input.

## Paid identity and complete source edit

Let EL and ES be the nonnegative raw LOAD and SWITCH edge words. The existing packing already computes

    bm=B-1, J=sum(edge_hat)-n, P=bm*J+1.

The old controller producers are

    dst=J-EL, src=dst-ES,
    left=src+P, right=B*dst.

They cost1M+3A. Their full left-minus-right residual satisfies the integer polynomial identity

    (J-EL-ES)+P-B*(J-EL)
      = (J-EL-ES)+((B-1)*J+1)-B*(J-EL)
      = 1+(B-1)*EL-ES.

Use instead

    flow_scaled_load=bm*EL,
    flow_switch_position=flow_scaled_load+1,

and compare flow_switch_position with ES. These two producers cost1M+1A. The paid comparison difference, square and final sum remain present; no finalizer operation is omitted. The residual itself has the same sign and the same value as before.

The [fresh helper](matrix193_controller_flow_scout.py) reconstructs all four removed definitions from the complete parent arrays and verifies that they have no external consumer beyond their one residual. It emits both new full arrays. Every other producer remains literal; only the two operands of the existing flow-residual row change. Exactly four rows disappear and two new rows are inserted. Packing, all63 native rows, the four coefficient words, all other comparisons, and the62-row finalizer remain otherwise literal. Both new arrays and all supplied ports are live.

A separate sparse expansion at formal B,J,EL,ES certifies the displayed equality, including the actual dependencies bm=B-1 and P=bm*J+1. Treating that proved equal residual as one shared formal atom, full expression interning checks every retained row and the final output. Consequently

    F_flow=F_composed

over every commutative ring with the same interpretation of the fixed integer numerals. No zero equation, one-hot assumption or division is used in this proof.

## Scope, degree and verification

The complete polynomials agree at identical input, fixed coefficients and witness values. Thus the ordinary-input projection, fixed-program recipe and every positive zero are preserved without a native witness reconstruction. The parent's exact degree transfers directly on every valid fixed-program slice. The larger naive gate-degree bounds remain only upper bounds; no new dense degree computation is needed. Arbitrary fixed-port assignments satisfy the algebraic identity, while the inherited simulation theorem still requires the valid recipe.

| Array | Packing | Native | Outer producers | Finalizer | Total | M | A | Witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Diagnostic |94|63|82|62|301|126|175|51|1,363|
| Actual fixed table |830|63|722|62|1,677|801|876|146|35,587|

The helper authenticates the immediate composed parent trio: Python `e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317`, JSON `a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37`, and proof `83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748`. It reads them only as bytes/JSON; no predecessor program is executed or imported.

Sixty-four fresh complete-source modular comparisons, across both arrays and two primes, check every retained register and the final output. Half bind the saved illustrative fixed coefficients and half vary all supplied ports. These are supplemental arithmetic checks, not native positive witness fixtures. The exact source identity is the proof. No giant outer trajectory or native Pell tuple is newly materialized.

The receipt contains both complete arrays, exact removed/new rows, the sparse identity certificate, full ledger and modular results. Parsing rejects duplicate keys and nonfinite values. Recursive receipt equality distinguishes types, and explicit guards remain active under optimized Python. Run the new helper with `--root` set to the absolute installed directory and `--expect` set to its JSON receipt; generation uses `--write`. Fresh normal and optimized replays from `/` pass.

The universal84 frontier is unchanged. Further coefficient evaluation improvements and positive controller-coordinate substitutions are separate candidates, not included in this packet.
