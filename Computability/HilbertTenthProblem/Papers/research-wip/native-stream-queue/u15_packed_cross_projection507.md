# Exact arithmetic across the U15 projections: 507 operations

Four elementary identities in the actual complete [511-operation compiler](u15_packed_composed_units511.md) save **two multiplications and two additions**, giving **507=209M+298A** operations for ordinary input and **319=116M+203A** for raw half tapes. The entire emitted polynomial is unchanged on all integer tuples. Every comparison residual, all native unit factors, the complete finalizer and every supplied coordinate are preserved.

The [source](u15_packed_cross_projection507.py) and [receipt](u15_packed_cross_projection507.json) also apply the same rewrite to the four reviewed [unit-partition representatives](u15_unit_partition_frontier.md):

| Parent operations / exact degree | New complete operations | Exact degree | Comparisons | Positive witnesses |
| --- | --- | ---: | ---: | ---: |
| 511 / 4881, one anchored group | **507=209M+298A** | 4881 | 25 | 87 |
| 513 / 3120, two SOS groups | **509=209M+300A** | 3120 | 26 | 87 |
| 515 / 2116, three SOS groups | **511=209M+302A** | 2116 | 27 | 87 |
| 517 / 1936, four SOS groups | **513=209M+304A** | 1936 | 28 | 87 |

This packet emits these four complete schedules. It does not repeat the parent's 4,140-form enumeration or claim a new global optimum. Their degrees follow from exact polynomial equality to the authenticated parents, including uniformity in the four fixed ordinary-input program numerals. The separate universal 87-operation benchmark is unchanged; the 87 in the witness column is a coordinate count.

## Four literal identities

Use the existing history registers `B=64D`, `P=(B−1)J+1`, `Dir`, `K29=1+P+...+P²⁸`, and the already paid powers `P²`, `P³`, `P⁵`. Nothing in the following algebra assumes a native equation, a dyadic radix, Boolean typing, positivity or a correct computation.

**1. Factor the direction mask: save one multiplication.** The source previously computed

```
v166 = Dir*(B−1)
v173 = v166*(P+1)
v174 = Dir*P²
v175 = v173+v174.
```

It now computes `(B−1)(P+1)+P²` and multiplies that sum by `Dir`. This is three operations instead of four, and preserves `v175` exactly. The three former internal registers have no other live arithmetic consumer.

**2. Factor J in the remaining mask: save one multiplication.** The other terms of `Mjoin` were

```
(D−1)J(P+1)P³ + (K29*J)P⁵.
```

The actual parent uses five multiplications for those two terms, followed by two additions to incorporate `v175`. The replacement computes

```
v262 = v175 + J*((D−1)(P+1)P³ + K29*P⁵).
```

It uses four multiplications and two additions, preserving the complete `Mjoin=v262`. Together, these factorizations express

```
Mjoin = Dir*((B−1)(P+1)+P²)
        + J*((D−1)(P+1)P³ + K29*P⁵).
```

**3. Fold the source-state offset: save one addition.** The actual affine controller defines `Qdev=binary83−6`; its only live consumer adds 7. Replace the chain by `v156=binary83+1`. The state comparison still has exactly its old operands and residual. The unused `Qdev` convenience register disappears.

**4. Compute the write-only contribution where it is consumed: save one addition.** In the actual controller DAG, let `a=binary28`, `b=binary14`, and `c=binary15`. Its paid source identities are

```
W=a+b+c−17,
WD=c−9,
W−WD=a+b−8.
```

The left tape expression uses `2W−(ZU+2WD)`. Replace it by `2(W−WD)−ZU`, using the two-addition source `a+b−8`. The old private three-addition source for W disappears. The multiplication by 2 remains paid, and the original `ZU+2WD` is still computed for the right tape equation, where it is needed. This preserves the complete left tape cut `v142`; it does not silently discard shared computation.

## Complete source identity and metadata

The four proof cuts are `v175`, `v262`, `v156`, and `v142`. For each cut the helper expands the actual old and new rows into exact sparse polynomials in explicitly listed independent atoms and checks equality. These local comparisons include all constants and offsets. A shared interning table then compares the complete old and new expression DAGs after replacing only those four proved cuts with common tokens. It additionally checks that every atom used by a local proof has the same upstream expression in both programs, preventing a changed cut input from invalidating composition.

This establishes equality of every comparison operand, every residual, all native factors, and the entire final output. No substitution valid only at zeros is used. The generic `rewrite(packet)` enforces the literal local row contract, exact source types, source closure and this complete proof. For an arbitrary supplied packet it claims only the algebraic rewrite; the canonical builders separately authenticate the parent computational theorem.

All 13 pruned register names are listed in the receipt. Five formerly exposed convenience names—`W`, `Qdev`, `direction_mask`, `range_mask`, and `Mc`—are now explicitly historical formulas in `proof_only_eliminated_registers`. They are not extra coordinates or uncharged source gates. Active register metadata instead provides `WminusWD` and `Qdev_plus7`, alongside the unchanged current joins, powers, native ports and supplied-coordinate interfaces. The former affine and composition metadata are archived under `pre_cross_projection_metadata`; current `full_polynomial_identity=True` refers to this packet's immediate authenticated parent.

No unit comparison is newly combined or deleted. The ordinary grouped packet still contains the six protected norm factors and the sole unrestricted checksum; their literal polynomial values are unchanged. Thus their existing modulo-four negative-unit exclusions, integer product argument and complete anchor/SOS zero-set theorem transfer directly. All partition group maps and retained comparison maps remain current because comparison order and values are unchanged.

## Paid schedules and exact degree

Every emitted binary addition, subtraction and multiplication costs one, including constant multiplication. Constants and copies are free. The finalizer is retained literally, and every emitted gate is checked to reach its output.

| Complete parent mode | New certificate | New complete polynomial | Exact degree |
| --- | --- | --- | ---: |
| Raw, ungrouped SOS | 289=105M+184A | 321=116M+205A | 1936 |
| Raw, grouped SOS | 290=106M+184A | 319=116M+203A | 3464 |
| Ordinary, ungrouped SOS | 427=178M+249A | 519=209M+310A | 1936 |
| Ordinary, grouped anchor | 433=184M+249A | 507=209M+298A | 4881 |

The four partition representatives have certificate costs 433,432,431,430 respectively, each with249 additions and184,183,182,181 multiplications. Their complete costs are shown in the first table.

Exact degree needs no new cancellation or modular argument: the complete polynomial is identical to its parent, and the receipt carries the parent's authenticated exact-degree certificate. The integer identities also imply equality of the polynomials as formal integer polynomials. The literal source ledger separately recomputes conservative degree upper bounds; for example the 507 form's literal bound is5019, while the transferred exact degree is4881. It keeps `exact_degree_claimed=False` in that conservative ledger and supplies the exact claim in `exact_degree_certificate`, with provenance and the full parent certificate. No exact-degree statement is inferred merely from a syntactic upper bound.

## Domains and computational scope

The raw interface still accepts natural supplied half tapes `L0,R0` and51 strictly positive witnesses. The ordinary interface still has positive `x`, four fixed positive program numerals and87 positive witnesses, including the complete input loader. The unchanged effective valid-program-slice qualification applies: arbitrary positive program tuples are not asserted to encode programs. No external computation horizon is introduced, no time decoder is omitted, and no native witness is refreshed or projected in this step.

Because the complete polynomial is identical, both its entire integer zero set and its restricted natural/positive zero set are identical on the same coordinates. The underlying computational theorem remains on the parent's stated domain. Algebraic equality outside that domain does not turn unrestricted signed zeros into valid computations.

The scout also checked the nearby input-recoder truth-field idea against the prior computed-field obstruction: its output congruence admits arbitrarily large representatives, so positivity of erased truth fields cannot be assumed. That route is not used. The present improvement is confined to the four exact source identities above, rather than a conjectural native-kernel change or controller-only count.

## Canonical API and replay

The two immediate source pins are:

```
u15_packed_composed_units511.py
234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38
u15_unit_partition_frontier.py
8e0514876e26b716e792dd7d8332c773fe15989eb558fc7e4fedff8046249ccf
```

Their bytes are authenticated before direct compilation/import. Eight independent type-sensitive hashes authenticate the actual complete parent descriptors, including data produced by dependencies; source hashes and inherited lineage are rechecked on warm-cache public access. Public packets, source lists and parent descriptors are defensive copies. `checked` rejects changes to the full canonical metadata, source, finalizer, counts or certificate, including equal-valued float/Boolean substitutions.

The APIs are:

```
build(ordinary=False, *, grouped=True, root=None)
build_frontier(index=3, *, root=None)    # exact integer index 0,1,2,3
checked(packet, *, root=None)
canonical_parent(packet, *, root=None)
polynomial_source(packet, *, root=None)
evaluate(packet, values, *, signed=False, root=None)
identity(packet, values, *, signed=False, root=None)
rewrite(packet)                         # locally guarded exact arithmetic only
```

`build()` selects raw319; `build(True)` selects ordinary507; `build_frontier()` defaults to ordinary513/degree1936. Flags require exact Booleans. Public evaluation requires exact integers and the stated semantic domain, or explicit `signed=True` for algebraic integer evaluation. There is no floating-point evaluator or proof-assistant certification claim. The inherited research compilers require assertions enabled.

From the maintained directory, or with an explicit dependency directory:

```sh
python u15_packed_cross_projection507.py --root /path/to/native-stream-queue
```

Default replay compares the saved receipt with exact types; `--write` deliberately regenerates it. The author checks all eight complete sources,256 integer identities including128 signed cases,5,856 comparison residuals,32 rational polynomial identities, malformed packet/scalar/local-transform rejection, public copy isolation and raw zero-half-tape boundaries. The sparse cut proofs and complete DAG proof establish the all-value result; finite evaluations corroborate it. No huge Pell witness or complete universal accepting zero is materialized.
