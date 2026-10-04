# Pack positive edge hats directly to save 72 operations

The complete fixed-table polynomial now costs **2,390=1,134M+1,256A operations**, with the same **150 positive witnesses** and exact degree **35,587** as the [balanced-output parent](matrix193_balanced_output_scout.md). It saves72 operations, trading82 fewer additions/subtractions for10 additional multiplications. The entire polynomial is unchanged on identical supplied coordinates, over every commutative ring.

The small diagnostic costs303=126M+177A with55 witnesses and degree1,363: one operation more than its parent. The saving depends on the fixed99-edge table. The overall universal84-operation frontier is unchanged.

## 1. Removing individual edge shifts from the packed words

Write h_e for the positive supplied edge_hat_e. The parent computes every E_e=h_e-1, then forms its sums and packed words. The new source uses

    J=sum_e h_e-n,
    Controller=sum_e h_e Q^e-R_n(Q),
    R_n(z)=1+z+...+z^(n-1).                             (1)

Both expressions are identically the old sum and controller word. The LOAD and SWITCH values E_0=h_0-1,E_1=h_1-1 remain separately paid, because the population, control flow and context-switch corrections need them. No raw value for another edge needs to be materialized merely to pack it.

For each fixed group g let I_g be its edge set, m_g=|I_g|, and

    H_g=sum_(e in I_g) h_e, S_g=H_g-m_g.

Groups may overlap between the X and Y blocks exactly as in the parent; each sum uses its actual saved edge set. For local group number g and t=Q², the duplicated selector block becomes

    S_block=(1+Q)*(sum_g H_g t^g-C_block(t)),
    C_block(t)=sum_g m_g t^g.                           (2)

Expanding h_e-1 proves (2) on all supplied values. The fixed correction polynomial is paid as arithmetic in the computed Q; it is not supplied as a free variable or obtained by division. The two identical expressions (1)–(2), plus the two retained raw edges, replace every changed edge-derived value.

The source keeps D=x+Hfix+height_slack, B=K*D, P=(B-1)J+1, Q=C*P and Qhalf=(C/2)*P with their prior meanings. All eight fixed program coefficients, the fixed padding C=2^93, group order, matrix coefficients, selected blocks and supplied extraction coordinates remain unchanged.

## 2. The fixed cardinality corrections are short

In the actual X block there are72 groups. Their multiplicities are one except for:

| Local groups | Multiplicity |
|---|---:|
| 7–9 and25–27 |3|
| 31–33,49–51 and55–57 |2|
|70|4|

These are counts of the authenticated edge lists, independent of program coefficients, ordinary input and witnesses. Thus the exact polynomial is

    C_X(t)=R_72(t)
           +t^7 R_3(t)*[(1+t^18)(2+t^24)+t^48]
           +3t^70.                                    (3)

For example, the bracket expands to2+2t^18+t^24+t^42+t^48, producing precisely the five exceptional triples after multiplication by t^7 R_3. The standalone emitter uses this schedule only after an exact match to all72 multiplicities. It retains a generic finite run-based schedule for the other saved layout.

All97 fixed Y groups, including LOAD, have one edge. Therefore

    C_Y(t)=R_97(t)=R_98(t)-t^97.                       (4)

The already required physical history mask uses R_98(t), including SWITCH, while Q^194=t^97 is also needed by the selected-block bound. Equation(4) shares those values. The diagnostic's one-group blocks use the constant correction1 directly.

Every power and repunit in (1)–(4) has a fixed exponent. The helper emits binary multiplication/addition schedules for them and counts every live gate. It introduces no duration-dependent exponent, division, digit-extraction primitive or new arithmetic oracle.

## 3. Whole-polynomial identity and inherited soundness

Let F_hat be the new full polynomial and F_balanced the parent. Equations(1)–(4) give the same J, controller word, both duplicated selector blocks, and retained LOAD/SWITCH values. All downstream packing formulas therefore give the same H,M,Z,q, global sum and time scale P. In particular all six native cuts agree before imposing any norm, typing or input equation.

The four signed coefficient polynomials are unchanged. The centered blocks Z_block-(D-1)S_block and every balanced extraction expression are consequently unchanged, as are all four history increments, controller flow and marked-population expressions. Thus all twenty outer residuals agree. The native63 rows and complete62-row finalizer have the same algebraic definitions at these equal values. This proves

    F_hat=F_balanced                                  (5)

over the integers and every commutative ring, with the identity map on **all** supplied coordinates. In particular the old high-positive/high-negative ports, low/dot offsets and slacks are retained literally in this packet.

The full positive zero sets, ordinary-input language and fixed-program recipe transfer directly through (5). No new native bootstrap or witness selection is needed. The proof does not appeal to a typed trajectory when removing the edge shifts, and does not claim that arbitrary values of the fixed coefficient ports are programs. The parent's x=0 boundary and ordinary positive-input restriction are preserved.

## 4. Complete arithmetic and degree

| Array | Packing | Native | Outer producers | Finalizer | M | A | Total | Positive witnesses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Diagnostic |94|63|84|62|126|177|303|55|
| Actual fixed table |830|63|1,435|62|1,134|1,256|2,390|150|

Stage counts use the emitted topological order; fixed powers first built in the new packing stage are reused by extraction later. All rows and supplied ports are live. The actual array has685 distinct integer literals, maximum magnitude C=2^93, with94 bits. The new numeral99 pays for the total hat shift; no nontrivial constant use is omitted.

Equation(5) transfers the parent's exact degrees35,587 and1,363 uniformly to every admissible fixed-program specialization. The naive gate upper degree for the actual source is36,539, six above the parent's36,533: the subtraction R_98(t)-t^97 deliberately cancels its leading term, which the naive recurrence misses. Neither bound is the actual polynomial degree. The full identity proves that no such cancellation changes the already established exact degree.

This packet does not incorporate the separate bounded-high witness chart or the separate structural coefficient-word compiler. Those changes require their own source composition and accounting.

## 5. Exact source evidence and limits

The [fresh helper](matrix193_hat_packing_scout.py) and [receipt](matrix193_hat_packing_scout.json) save both complete arrays. Nine predecessor files are authenticated as inert bytes or JSON. No predecessor Python or historical suite is executed or imported. The new helper contains its own copied emitter and new arithmetic, structural checks and exact polynomial audit.

| Artifact | SHA-256 |
|---|---|
| Python | `0f1df101e2e7eb598c5252ecc676289ecc984ee2fee321f66471a225fabec8f6` |
| JSON | `7ba450619fac0d057c33a5d4a64ff18f78a922b5bea8637db269d7b8584a221c` |

The exact audit separately compares the paid D,B,P,Q definitions, full J and Qhalf expressions, all four coefficient words, all six native cuts and all twenty full outer residuals. It uses sparse integer polynomials at explicit paid cuts, verifying each cut before using it in later identities. The four coefficient words are compared in full before their equal outputs become shared atoms. Literal checks of all63 native rows and all62 finalizer rows then lift these identities to the complete output. This is an exact coefficient argument, not a conclusion from modular samples.

Supplementary checks include32 complete source/direct-formula modular evaluations, ten diagnostic outer histories through every literal nonnative row, and a complete dense diagnostic specialization. The actual saved83-TILE+SWITCH fixture checks all twenty mathematical outer comparisons and has the same H/M/Z/q digest `69354b5e33fc40c1990a31713d5ae17b53265374f1590b2ae26b6082f983f610`. Its huge literal outer DAG is not evaluated exactly, and no native Pell tuple is materialized. These scopes are unchanged from the balanced parent.

The parser rejects duplicate JSON keys; receipt comparison is recursive and type-exact, and explicit checks remain active under optimized Python. Reproduce from any working directory:

```sh
hat_wip=/absolute/path/to/native-stream-queue
python3 "$hat_wip/matrix193_hat_packing_scout.py" \
  --root "$hat_wip" --expect "$hat_wip/matrix193_hat_packing_scout.json"
python3 -O "$hat_wip/matrix193_hat_packing_scout.py" \
  --root "$hat_wip" --expect "$hat_wip/matrix193_hat_packing_scout.json"
```
