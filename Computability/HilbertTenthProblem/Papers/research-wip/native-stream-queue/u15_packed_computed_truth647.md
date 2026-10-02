# Paid disjoint tags reduce the complete U15 polynomial to 647 operations

The [compiler](u15_packed_computed_truth647.py) emits a complete ordinary-input polynomial with **647=253M+394A operations, 46 comparisons and 102 strictly positive witnesses**. Its raw natural half-tape interface costs **404=145M+259A**, with11 comparisons and51 positive witnesses. Both have formal degree at most1936. The [receipt](u15_packed_computed_truth647.json) includes all gates, comparisons, witness names and complete finalizers for both interfaces, together with their fully emitted tagged parents.

This is a six-operation reduction from the complete [653-operation packed U15 history](u15_packed_two_tape_history.md). It adds three paid tag gates and deletes three comparison finalizers. The five arithmetic gates that reconstruct three truth fields replace exactly five obsolete checksum/input-sum gates. The established global universal-polynomial bound remains87. This packet does not include the independent state-relabeling optimization.

## 1. Retained pretyping bounds

Use the baseline's actual29-rule U15 controller, natural initial tapes L0,R0, positive edge hats, and computed geometry

```
J=sum_i(edge_i-1),  D=L0+R0+height,  B=64D,
P=(B-1)J+1,  T=P^34.
```

All five outer comparisons, both range lanes, all controller lanes and the three selection lanes are retained. Write the baseline joined words as A,M,Z; its AND scale is `cap=B*T`. The retained head and aggregate-bound equations are

```
B*U=S+P,
H+G+ZL+ZR+ZU+bound=P.
```

Before any AND, power, norm, or Boolean typing theorem is used, positive supplied coordinates imply D>=1, B>=64 and J>=0. The aggregate bound excludes J=0 and gives P>=B and each of H,G,ZL,ZR,ZU below P. The fixed linear projection satisfies S<=J on every supplied tuple, so the head equation gives U<=J<P. Every edge word is at most J<P. The remaining masks satisfy `(B-1)*Dir<=P-1` and `(D-1)*J<P`. Consequently every joined chunk is below P and

```
0<=A,M,Z<T.
```

This is exactly the earlier pretyping argument and uses neither the tape/state equations nor the imported AND conclusion. In particular the aggregate bound does not silently assume that a selected field is already below its associated tape field.

## 2. Three paid tags

Define

```
twice_T=2*T,
A'=A+twice_T,
M'=M+T,
Z'=Z,
cap'=cap=B*T.
```

These are exactly one multiplication and two additions. The base scale is unchanged. Before power typing, the inequalities above give A'<3T, M'<2T and Z'<T, hence all inputs and output are below cap because B>=64.

After the paid AND theorem establishes that cap=B*P^34 is dyadic, both B and P are dyadic and therefore T is dyadic. The separate binary prefix tags2 and1 are disjoint. For these typed lanes,

```
(A+2T) AND (M+T) = A AND M.
```

This equality also proves the converse implication, with no assumption on A AND M in advance. Thus the tagged AND is equivalent to the baseline joined AND at the same complete outer assignment and scale.

Here and below, “native coordinates” means the history kernel coordinates with names starting `native__`. All ordinary loader witnesses, including its own internal recoder coordinates, stay unchanged.

The scale being unchanged does **not** make the private native witnesses unchanged. The packed truth-field index changes with the input ports. The relation to the baseline is equality of the positive zero relations after forgetting **all history native__** private coordinates (the ordinary loader witnesses stay unchanged), using fresh full positive native extensions in each direction. No pointwise polynomial identity or coordinatewise graph map to the untagged baseline is asserted.

## 3. Positive computed truth fields without circular typing

Let the native padded registers and scale be

```
padded_A=16A'+12, padded_B=16M'+10,
F3=16Z'+8, q=16cap.
```

Replace the three supplied positive coordinates F0,F1,F2 by five subtraction gates:

```
F1=padded_A-F3,
F2=padded_B-F3,
t0=q-padded_A,
t1=t0-F2,
F0=t1-1.
```

The constant in the last closed form is **minus15**:

```
F1=16(A'-Z')+4,
F2=16(M'-Z')+2,
F0=16(cap-A'-M'+Z')-15.
```

The pretyping inequalities from Section1 prove positivity before any native theorem is applied:

```
F1 >= 16(T+1)+4,
F2 >= 18,
F0 >= 16((B-5)T+2)-15 > 0.
```

For the last bound, `cap-A'-M'+Z'=(B-3)T-A-M+Z >= (B-5)T+2`. The native scale q is positive and F3>=8 independently. Thus every reconstructed coordinate satisfies the original strictly positive native contract before invoking its Pell, power or AND conclusions. There is no use of AND typing to justify the subtractions that are needed to invoke that typing.

## 4. Exact graph identity to the tagged parent

The fully emitted tagged parent retains all three original coordinates and comparisons. Its deleted comparison differences are

```
F0+F1+F2+F3+1-q,
F1+F3-padded_A,
F2+F3-padded_B.
```

Under the five definitions in Section3 they vanish as literal integer polynomial identities. The old intermediate rows `input_A,shared_sum02,bs_Q,bs_q,input_B` have no surviving consumer after these comparisons are removed. They are replaced by exactly the five new subtraction rows. Every other source gate and comparison is retained, with identical inputs on the graph restoration. Therefore the **entire** old tagged-parent sum-of-squares polynomial, evaluated after restoring F0,F1,F2, equals the entire new polynomial on every signed integer assignment, including assignments outside all semantic bounds. The strong native auxiliary residual is kept exactly; no norm identity valid only at zeros is substituted into it.

On every new positive zero the retained head and aggregate equations hold, so Section3 restores positive F0,F1,F2. This gives a unique positive tagged-parent zero. Conversely those three parent comparisons uniquely force the definitions, and dropping the three coordinates from any tagged-parent positive zero gives the child zero. Restoration and deletion are inverse. This is a bijection with the **tagged parent**, distinct from the existential equivalence with the untagged baseline explained in Section2.

The baseline first-halt proof then applies in full: the scalar AND pays the dyadic radix and common duration; controller lanes give one actual instruction per cell; copied range lanes bound tape digits below D; selected lanes pay all products; state/head equations give chronology and endpoints; the packed tape comparisons have coefficients strictly smaller than B. There is no supplied horizon, tape-typing assumption, order oracle or unpaid condition. The earlier coefficient-two false-pop alias remains excluded by the retained range lanes.

## 5. Ordinary input and complete ledgers

The ordinary interface preserves the entire paid width32 recoder and raw half-tape loader, with the same alias L0=program_L and shared positive initial right tape. Input-padding length remains independent of the packed history duration. For every c.e. set of positive integers, the earlier effective program recipe supplies four fixed positive numerals such that membership is equivalent to the existence of102 positive witnesses annihilating this single fixed polynomial. Arbitrary positive program quadruples are not asserted to encode valid programs.

| Interface | Certificate | Comparisons | Positive witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Raw natural L0,R0 |372=134M+238A|11|51|404=145M+259A|
| Ordinary positive x, fixed program numerals |510=207M+303A|46|102|647=253M+394A|

The tagged parent costs413 raw or656 ordinary, with the baseline14/49 comparisons and54/105 witnesses. Deleting three comparison differences, three squares and three summation additions saves9 operations. Its five deleted arithmetic rows are replaced by five computed-field rows, so the certificate cost is unchanged from the tagged parent. Relative to the untagged baseline the three tag gates remain paid, for a net saving of6.

Every emitted binary addition, subtraction and multiplication costs one, including fixed coefficients. Constants and copies are free. All gates reach the final output. Literal degree propagation through the complete emitted source gives an upper bound of1936 in both interfaces with fixed program numerals of degree zero. The bound does not use any equation that holds only at a zero, and no exact-degree or arithmetic-minimality claim is made.

## 6. Public contracts and source authentication

`build(ordinary=False)` returns a defensive copy of the complete child packet; `tagged_parent(ordinary=False)` returns a separate defensive copy of its exact graph parent. `checked` and `checked_tagged_parent` require the entire corresponding canonical packet with exact scalar and container types. `evaluate` and `evaluate_tagged_parent` accept precisely their declared coordinate sets, exact integers, natural raw initial tapes and strictly positive other coordinates. Formal signed evaluation requires explicit `signed=True`.

`lift_to_tagged_parent(child_packet, values)` validates the child domain and requires the retained head and aggregate-bound equations, then restores the three positive fields. `project_from_tagged_parent(child_packet, parent_values)` requires the tagged-parent domain, those same two bounds, and all three graph comparisons before deleting the fields. These positive helpers operate on the explicitly proved pretyping cone; they do not claim positive graph restoration on every arbitrary positive false witness. In signed mode, restoration is defined on all exact signed assignments, while projection still requires the three graph equalities. Returned assignments are fresh dictionaries.

The imported baseline file is authenticated before execution by SHA-256
`ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318`.
The complete **actual raw and ordinary packets consumed from it** are also pinned by type-tagged structural hashes:

```
raw:      88bece7a25db1454f0c81574bbe40c3bb3d1a46bf5942fa0ccd62ffa0625e40a
ordinary: 43f6def9967bbbf36931386e66717f2c6a53c4488512cd3a47d6ccde9013634f
```

These pins cover source, comparisons, parameters, private coordinates and metadata, distinguishing integer, Boolean, scalar and container types. Thus a stale or substituted cached sibling loader cannot silently replace the consumed arithmetic while leaving the parent file hash intact. The parent's native-descriptor and loader-dependency guards remain in force. This is an arithmetic/source boundary guarantee, not a claim to sandbox arbitrary hostile Python code or arbitrary post-validation monkeypatching.

## 7. Replays and limits

Run `python u15_packed_computed_truth647.py` to compare a fresh receipt, or add `--write` to regenerate it. The script normally sits beside its pinned parent and dependencies. During isolated review it can find that directory through PYTHONPATH. Its research replay refuses optimized Python; the source and packet authentication checks themselves use explicit exceptions and remain active under optimization.

The author replay checks the actual29-rule primary table,160 complete independent residual/SOS and tagged-parent graph cases including80 signed cases,518 malformed rejections, four cold/nested copy cases,16 genuine outer positive graph restorations,128 changed outer coordinates,1,035 untyped margin boundary cases,5,461 exact typed tag identities and two cold changed-loader rejections. Both full source variants and both tagged parents are emitted in the receipt. Source closure, operation histograms, liveness, witness counts and degree propagation are checked for each packet.

The genuine history fixtures verify the complete outer equations and exact joined AND, and reconstruct positive truth fields. Their other private native coordinates are placeholders. They are explicitly **not** claimed full Pell zeros. Complete positive extensions are supplied by the already reviewed uniform native theorem; the ordinary loader likewise uses its complete uniform recoder converse. Finite tests supplement these all-value proofs and do not exhaust the unbounded relation.

The [independent review](review_u15_computed_truth647.md) records the full
source transformation, complete residual audit and positive composition proof.
