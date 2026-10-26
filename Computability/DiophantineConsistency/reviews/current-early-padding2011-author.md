# CurrentEarlyPadding2011 author verification

**Author verification: PASS; independent review remains separate.** Author: circuit_reduction. The complete 311-line module and 56-line focused checks were self-read before the final fresh runs. The imported frozen tail proof was also read completely; the clause packet received a separate independent full-source review and fresh replay. No frozen mathematical source, maintained page, or central document was changed.

## Frozen files and direct imports

Paths are relative to Computability/DiophantineConsistency.

| File | SHA-256 |
| --- | --- |
| Lean/DiophantineConsistency/CurrentEarlyPadding2011.lean | 13dd5214cba3f9d704e4617b3e1140353aaa4cc18c0fd02170153a308160c3ea |
| Lean/DiophantineConsistency/CurrentEarlyPadding2011Checks.lean | d7e0f4a7867c30de5c8b56c8cce9fd786117675aa794736b909d0e82a45e4bd9 |
| Lean/DiophantineConsistency/CurrentReflectedGeometry2011.lean | 268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1 |
| Lean/DiophantineConsistency/CurrentSelectorTail2011.lean | 2850d691a36e3e65ff3d5c666b343c4cc58f5445466792546939c0930e658830 |
| Lean/DiophantineConsistency/CurrentClause2011.lean | a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566 |

The new module object SHA-256 is 459d50a21a734defb935eb33590a366abc154fd8c6a7c671b4dfe11da34b1b44. Direct imports are exactly Geometry, Tail and Clause above. No CurrentCount or CurrentOneHot theorem is imported or assumed.

## Public endpoint

`CurrentEarlyPadding2011.padding_bindings` takes c, r, carry, digits on ZMod(N*2011), a cell base b with b.val%2011=0, and these explicit hypotheses:

- c is Boolean and is zero outside the actual periodic CurrentMasks2011.lowSupport;
- every temporal digit r is at most2^10 and is0 modulo16;
- every incoming/outgoing carry value is at most57;
- the exact local equality is convolution(folded,c,k)+r(k)+carry(k-1)=digits(k)+radix*carry(k);
- every digits(k) passes the actual full CurrentHighDigits2011.maskDigits(k) test.

For every j=1..483 it proves all three required bindings:

```text
paddingUnit(c,b,j) <= 2,
paddingDigit(digits,b,j) mod16
  = (2*prefixSum(f -> c(b+f),j) + paddingUnit(c,b,j)) mod16,
paddingDigit(digits,b,j) AND 8 = 0.
```

The functions are literal: paddingDigit is the normalized digit at b+(63+j), and paddingUnit is c(b+(63+j)-18)+c(b+(63+j)-2020). Thus a caller may choose this explicit paddingUnit as the existential u in the generic middle-phase padding interface. No supplied padding residue or mask is a premise.

There is no at-most-one selector premise, decoded label premise, temporal alignment premise, assumed zero carry, carry-division equation, or extra digit bound. In the intended phase7..10 application, Boolean rotation supplies the two temporal hypotheses. The exact local equality and nonnegativity of digits are sufficient to derive early carry resets.

## Proof construction and dependency order

1. For h<=546 and every coefficient position below459, Geometry.reflected_source makes its actual cyclic source value zero: h+position<1005, so the source lies outside the periodic support. Tail.tail_source_bound therefore bounds the entire reflected sum by the proved exact T459=137820284543942, before any selector-count recovery.
2. The three actual non-reflected kernel monomials contribute at most3 by Booleanity. Adding temporal<=1024 and carry<=57 gives raw+incoming<radix by the exact tail inequality. The local equality then forces outgoing carry zero through field546, without first assuming a digit bound or zero incoming carry. In particular every predecessor of fields64..546 resets.
3. Every doubled selector coefficient is2 modulo16 and every control coefficient is0 modulo16. The complete reflected sum therefore reduces to twice its selector-source sum, with no omitted collision.
4. At field63+j, a selector coefficient at physical position p has source j+p-942 if p>=942-j, and otherwise its source is absent. The actual proved physicalEquiv transports the sum to all p=0..941. The generic shifted_suffix_sum identity then identifies it with precisely the first j physical source bits. Its endpoints are j=1/source0 and j=483/sources0..482; no extra or missing endpoint occurs.
5. The bare marker1004 input vanishes by the same exact support geometry. The shared18 and spatial2020 inputs are retained in paddingUnit; the latter may come from the preceding cell and is not incorrectly treated as absent. Both are Boolean, giving unit<=2.
6. The normalized digit keeps the reflected-prefix residue because its predecessor carry is zero, radix is divisible by16, and r%16=0. This uses temporal divisibility rather than alignment.
7. The target field63+j has its exact nonzero residue in the padding band, including in later cells. Its full repeated high-mask digit is8, so the supplied global pointwise mask yields the actual bit-three test. No origin subtraction affects these fields.

These steps close the literal483-padding-premise gap of the preliminary-count argument. They do not themselves compose the actual polynomial zero with Boolean rotation and the all-phase clause theorem, nor do they prove tableau/halting or Con(ZFC) calibration. Those compositions remain separate modules.

## Fresh bounded verification

Final commands use Lean v4.32.0, `-M6000 -j1`, and Elab.async false. The new module object is written under its own previously unused path; no unrelated object was overwritten. Frozen prerequisites were reused, not claimed freshly rebuilt by these commands.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentEarlyPadding2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentEarlyPadding2011.olean
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentEarlyPadding2011Checks.lean
```

Module: PASS, exit0,6.43seconds, peak3289564KB, no diagnostics. Checks: PASS, exit0,3.19seconds, peak3235984KB. Logs: /tmp/earlypadding2011-final-module.log and /tmp/earlypadding2011-final-checks.log.

Focused checks establish the symbolic first prefix, actual cutoff tile866 at the last prefix, the physical941/source482 endpoint via the proved inverse permutation, an actual preceding-cell spatial input, absent marker residue1071, both actual full-mask endpoints in a later cell, and the temporal divisibility/reset bound at phases7 and10. All ten axiom reports contain only propext, Classical.choice and Quot.sound: shifted_suffix_sum, early_reflected_bound, early_carry_zero, selector_sources_eq_prefix, reflected_padding_residue, padding_convolution, padding_incoming_zero, padding_digit_residue, padding_mask and padding_bindings. No sorry, new axiom or native_decide was introduced.
