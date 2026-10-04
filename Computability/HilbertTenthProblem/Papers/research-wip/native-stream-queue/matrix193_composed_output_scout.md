# Compose the matrix packing improvements: 1,679 gates and 146 witnesses

The complete actual-table source has **1,679 = 801M + 878A gates**, **146 positive witnesses**, twenty outer residuals and exact degree **35,587**. It combines the three frozen improvements below and saves five further gates by sharing their already paid powers. The small diagnostic costs **303 = 126M + 177A**, with 51 positive witnesses and exact degree 1,363.

This is an improvement to the alternate uniform ordinary-input matrix route. Its 99-edge controller, fixed matrix table, 340 physical selection lanes, native kernel, ordinary-input bridge and fixed-program coefficient recipe are retained. The established 84-operation universal bound is unchanged.

## 1. Exact parents and emitted source

The three immediate parents are [hat packing](matrix193_hat_packing_scout.md), [structured coefficient evaluation](matrix193_structured_coefficient_scout.md), and [the bounded-high chart](matrix193_bounded_high_output.md). All descend from the same frozen [balanced-output source](matrix193_balanced_output_scout.md). The new [standalone helper](matrix193_composed_output_scout.py) and [receipt](matrix193_composed_output_scout.json) save both complete arrays; the count is taken from the actual live rows, not inferred by subtracting parent headlines.

| Pinned artifact | SHA-256 |
|---|---|
| Structured Python | `39ab5c942af5bd6d725d2c17e89d2222e3e44bf26cc59e3c1bad1d4e011e10a9` |
| Structured JSON | `ebdc03c29dc9469896aa858312c95400a77adf853116e6819c514fb4e587d032` |
| Structured proof | `8e49bed183eed196768951d3a86febc6cbd8d0a2e8898387c41b3b0e0ebeced3` |
| Hat Python | `0f1df101e2e7eb598c5252ecc676289ecc984ee2fee321f66471a225fabec8f6` |
| Hat JSON | `7ba450619fac0d057c33a5d4a64ff18f78a922b5bea8637db269d7b8584a221c` |
| Hat proof | `e424a750e626fd0d174692e13ad82b284949da22d49db1419fa20ec20ca111fd` |
| Bounded-high Python | `5ffccf1c76fcb27b1e68573a717c7fcb12f6e1d7afce47be2b2b30b54b2b6f63` |
| Bounded-high JSON | `9fee15c95d916813f425db0f306c9f0e50990540fe9284fc00c46cc380cb5039` |
| Bounded-high proof | `7f5a5bab9bff8518881a16a7c9d32916ce4ca1ff9dcbaa18f7fab7d452da654c` |
| Common balanced JSON | `63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf` |
| Common balanced proof | `cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde` |

All eleven files are authenticated. The three receipt source hashes are also checked against their pinned Python bytes. Predecessor files are read only as text or JSON; no predecessor Python is imported or executed. The new helper adapts the hat packet's sparse ring-audit routines by source copying and adds a new literal composition, coefficient transplant, port audit and full-source checks.

## 2. The composition and five additional shares

Start with the complete 2,390-gate hat-packing array. It packs the positive edge hats directly, with paid fixed repunit/cardinality corrections, retaining precisely the old packing functions on every supplied tuple. Its four coefficient words still use the old 1,344-row Horner cones.

The structured parent supplies a complete 638-row replacement for those four words. It factors the actual 22 X and 29 Y word triples, and verifies every coefficient in the resulting polynomials. The component depends only on the paid scale Q and twelve other paid pure-Q values. For each external dependency, the new helper expands its complete integer polynomial in Q and finds an equal register in the hat-packing prefix. It then processes every component row in order, reusing an existing register only when the full coefficient lists agree.

This discovers five further paid shares:

| Structured component row | Hat-packing register | Exact value |
|---|---|---|
| `cp292` | `r169` | Q^17 |
| `cp293` | `r170` | Q^34 |
| `cp632` | `r190` | Q^97 |
| `cp633` | `r191` | Q^194 |
| `cp634` | `r192` | R_97(Q²) = R_98(Q²) − Q^194 |

These save four multiplications and one subtraction. No polynomial value is supplied freely: every reused register already has a paid definition in the emitted prefix, and those rows remain live. The component therefore has **633 live rows = 339M + 294A** in the composition. Exactly 1,344 old Horner rows become dead, with no other hat-parent row deleted. Complete coefficient expansion proves the four replacement cuts, including all zero and signed coefficients.

Finally, in each of the four high-quotient rows, replace

    high_positive − high_negative

by

    high_hat − T_half,

where T_half is the already paid half-scale for that block. This remains one subtraction per row. The four high-positive/high-negative pairs are replaced by four positive high hats, reducing 150 witnesses to 146. All other supplied coordinates retain their names and meanings.

The small diagnostic lacks the actual U15 triple structure. It uses the generic hat-packing schedule and the same four high substitutions; no structural coefficient saving is attributed to it.

## 3. Whole-polynomial identity to the bounded-high parent

Let F_C denote the new complete polynomial and F_H the frozen bounded-high polynomial. They have the same supplied coordinates. The composition proves

    F_C = F_H                                                   (1)

over every commutative ring, with the same interpretation of all integer numerals and fixed coefficient ports.

The fresh exact audit establishes (1) in the following order. It first compares the paid definitions of D, B, P and Q, and then J and Qhalf. In particular the hat formula J=sum(edge_hat)−n equals the old sum of edge_hat−1 before imposing any positivity or zero equation. It expands all four coefficient words in full and only then replaces each equal pair by a common formal atom. At those proved cuts it compares all six native packing inputs and all twenty complete outer residuals as sparse integer polynomials. Finally it checks the actual 63 native rows and every row of the 62-gate SOS/product finalizer against their common definitions.

Thus neither native typing nor a trajectory promise is used to establish the arithmetic identity. The fixed-program recipe is still needed to apply the inherited universal simulation and positive-zero theorem. The proof does not say that arbitrary eight fixed-port values encode programs.

In particular the ordinary input, all state/edge coordinates, both selected-block hats/slacks, low and middle offsets/slacks, high hats, native witnesses, height and global slacks, terminal fields and population quotient have identical positive-zero projections between F_C and F_H. No further native witness selection is needed when passing between these two polynomials.

## 4. Positive pullback to the balanced parent

For completeness, write F_B for the common 2,462-gate balanced parent, which has two positive ports for each high quotient. For a block of length l, put

    T=Q^(l−1), T_half=Qhalf*Q^(l−2), Qhalf=(C/2)*P.

The actual lengths are 144 and 194, and the diagnostic length is 2. The fixed padding C is even and positive. On the valid positive domain, every edge hat is at least one, so J>=0, P=(B−1)J+1>=1, and Q=C*P>=C. Therefore every T_half is a strictly positive integer independently of the zero equations.

For every commutative ring the complete pullback is

    F_C = F_B(high_positive=high_hat,
              high_negative=T_half),                         (2)

with the same substitution for all four products and every other coordinate retained. The helper first reconstructs the frozen bounded-high source from exactly these four row edits; (1) then gives (2). On positive tuples the substituted parent ports are positive, so every new positive zero maps directly to a positive balanced-parent zero.

Conversely, a positive balanced-parent zero has typed centered digits and balanced convolution coefficients c_h satisfying |c_h|<=Q/2−1. Its unique high quotient obeys the entire-tail bound

    |high| <= (Q/2−1)*(T−1)/(Q−1) < T/2 = T_half.

Hence high_hat=high_positive−high_negative+T_half is strictly positive. It reproduces the same high quotient, all retained cuts and every complete residual. This produces a positive F_C zero with the same ordinary input and every other non-high supplied coordinate.

The comparison with F_B excludes both old high ports and the new high hat. It is a projection equivalence, not a bijection of full witness tuples: the old common offset of the high pair was free. The low/dot extraction hats and slacks are retained in this transition. The parent's zero-input boundary, absent LOAD case and ordinary positive-input restriction are unchanged.

## 5. Exact degree and complete ledger

Identity (1) transfers the bounded-high parent's exact degrees directly. Its degree argument also remains visible in the new source. For the longest block let l=194, let S_last,top be its final group-selector leader, and let a0 be the first forward coefficient of the corresponding reverse word. With fixed program numerals treated as constants,

    D_top=x+height_slack,
    J_top=sum(edge_hat), Q_top=C*K*D_top*J_top.

The leading part of an extraction residual is

    D_top*Q_top^(2l−2) * ((C*K/2)*J_top − a0*S_last,top).        (3)

The high shift causes a tie at degree 4l−2; it cannot be ignored. The mandatory SWITCH edge occurs in J_top and is absent from the final selector of either fixed block. Therefore its coefficient in the bracket in (3) is C*K/2, which is nonzero on every valid fixed recipe. The helper checks this literal edge exclusion and the positive even padding. The residual degree is exactly 774, its real SOS has degree 1,548, and the unchanged nonzero native product has degree 34,039. The final exact degree is 35,587. The diagnostic gives 6, 12 and 1,351 respectively, hence degree 1,363.

| Complete array | Packing | Native | Outer producers | Finalizer | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Diagnostic | 94 | 63 | 84 | 62 | 126 | 177 | 303 | 51 | 1,363 |
| Actual fixed table | 830 | 63 | 724 | 62 | 801 | 878 | 1,679 | 146 | 35,587 |

The actual source has 241 distinct integer literals, in addition to the eight fixed coefficient ports. All paid rows and all supplied ports are live. The naive gate-degree upper bound is 36,547; it is not the exact polynomial degree because it does not account for the proved cancellations. The actual route saves 783 operations and four positive witnesses from balanced 2,462/150, without changing the ordinary-input language or degree.

## 6. Replay evidence and boundaries

The receipt contains both full sources, all changed port sets, all thirteen external pure-Q dependency matches, the five reused registers, the four full coefficient lists, the exact retained native and outer identities, complete liveness/count checks, and the SWITCH degree certificates. Thirty-two fresh signed whole-source comparisons over two prime fields compare every native cut, all twenty residuals and the final output against the bounded-high parent. Half use the saved valid fixture coefficients; half vary all fixed ports as well.

The large 84-cell outer fixture recorded in the bounded-high receipt is copied solely as inherited evidence and explicitly marked not replayed here. No new giant trajectory, literal giant outer-DAG evaluation or native Pell tuple is claimed. The arithmetic identity and positive maps, rather than a new sample history, transfer the established ordinary-input theorem.

After all dependencies are installed together, run:

```sh
composed_wip=/absolute/path/to/native-stream-queue
python3 "$composed_wip/matrix193_composed_output_scout.py" \
  --root "$composed_wip" --expect "$composed_wip/matrix193_composed_output_scout.json"
python3 -O "$composed_wip/matrix193_composed_output_scout.py" \
  --root "$composed_wip" --expect "$composed_wip/matrix193_composed_output_scout.json"
```

For staging, `--artifacts` explicitly names the directory containing the three immediate trios; the two common balanced dependencies are still read from `--root`. Omitting it uses `--root` for every file. Generation uses `--write` instead of `--expect`. The parser rejects duplicate JSON keys, full receipt equality is recursive and type-exact, and every check remains active under `-O`.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass on the frozen helper and receipt, using the explicit staging directory. No predecessor code was executed.
