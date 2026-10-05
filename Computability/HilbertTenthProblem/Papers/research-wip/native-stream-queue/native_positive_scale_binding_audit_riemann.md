# Static binding audit of the prescribed positive-scale native component

The saved standalone packet passes an independent static row, interface, topology, consumer and liveness audit. The exact variant is `example` in `native_binary_positive_scale.json`. Its `source` contains the entire 108-row standalone polynomial, not just the 64-row certificate. No row was evaluated numerically or symbolically.

The receipt SHA256 is `ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628` (10,877 bytes). The full proof note, read in the preceding review task, is SHA256 `d958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97`. Exact structural data and consumer lists accompany this note.

## 1. Exact field schema and native cut

The JSON root has `status`, `ledger`, `audit`, `inverse_typed_scalar_cases`, `rejected_guard_mutations`, `source_sha256`, `example` and `scope`. Only `example` supplies this standalone source. It has five fields: `source`, `comparisons`, `parameters`, `auxiliaries` and `output`.

Every source row is a four-element JSON list `[name, op, left, right]`. The operation is one of `+`, `-`, `*`; an operand is either a string register/interface name or an integer literal. All definitions are unique and topologically available. The supplied parameters and auxiliaries have disjoint names. All parameters, all auxiliaries and every row are live.

Rows 0 through 63, using zero-based indices, are the complete certificate: 33 multiplications, 23 additions and 8 subtractions, hence 64=33M+31A. Every certificate row reaches a comparison endpoint. The distinct literal integers are 1,2,3,4,6,8,16. This is a literal-token census, not a claim about an optimized whole-wrapper numeral-role count.

Rows 64 through 93 are the fifteen comparison differences and their squares. Rows 94 through 107 accumulate the squares. Every row matches the stated comparison order literally, and the final output is `sos_sum14`. The complete 108 rows have 48 multiplications, 37 additions and 23 subtractions, hence 108=48M+60A. Every row reaches that output. A fresh combined wrapper can retain the 64-row native certificate and its comparisons, omit precisely this old standalone finalizer, and emit one fresh combined finalizer. It must not treat all 108 rows as the certificate.

The receipt's `source_sha256` is `f119d8630c028798a691963f65913aba82db37e346733b24ad02bd16a363aa02`. It matches SHA256 of the UTF-8 text returned by default `json.dumps(example.source)`, including its ordinary spaces. For unambiguous additional pins, compact JSON of the 64-row prefix has SHA256 `a8664f604ae0e4cacadd1293cd0deeddcb3c2371b4618d7ab26c8f954741a5bc`, and compact JSON of all 108 rows has SHA256 `a28770f101ce99d6c3ffc3e69509d1991d332fc7c694b710f754211020b289fe`.

## 2. All supplied roles and comparison endpoints

The four parameters, in order, are `P,Hhat,Mhat,Zhat`. The 21 positive auxiliary names, in order, are

    F0,F1,F2,a,c,d,f,h,i,j,k,o,r,s,tau,eta,zeta,ga,
    y_aux,odd_half,bound_beta.

In the geometry wrapper, native `P` must bind to the outer top scale T=P_lane^(8m+2), not the outer lane radix P_lane. The remaining parameters bind to A_pack+1, M_pack+1 and Z_pack+1. Their values are positive by the already reviewed pretyping proof. The native component's exact positive-zero projection is dyadic T, 0<=A_pack,M_pack<T and Z_pack=A_pack AND M_pack, with full positive converse.

All 15 comparison pairs, in their saved order, are:

    (r,bs_packed), (bs_q,q), (s,bs_odd), (L9,R9),
    (c,R10a), (k,R10b), (k,R11), (a,R12), (d,R14),
    (L15,R15), (ic22,R16), (L17,P17), (H17,aux_u_rhs),
    (input_A,padded_A), (input_B,padded_B).

Every endpoint exists in the certificate or supplied interface. Both padded input comparisons remain required, as do the checksum, oddness, strong auxiliary and all other native comparisons. The supplied raw `r` remains an auxiliary; it has not been graph-substituted by this variant. There is no supplied `w`: the positive-scale coordinate is `bound_beta`, used with `r` to compute `bs_X_bound`, then `wn2=bs_X_bound*q`.

All native auxiliary names and every native computed name must be freshly prefixed before composition. Prefixing only witnesses is insufficient: names such as native `A`, `H2` and `F1` can collide with outer packs, histories or terminals. Integer literals and operations remain literal; the four relation parameters are replaced by their declared bindings rather than introduced as extra witnesses.

## 3. Complete input-padding consumer boundary

The first seven rows are exactly

    q        =16*P
    scaled_A =16*Hhat
    padded_A =scaled_A-4
    scaled_B =16*Mhat
    padded_B =scaled_B-6
    scaled_Z =16*Zhat
    F3       =scaled_Z-8.

Each parameter occurs in just its displayed multiplication. Each `scaled_*` register has exactly its one displayed consumer. `padded_A` is used only by comparison 13; `padded_B` only by comparison 14. `F3` is consumed by rows 7 (`input_A`), 11 (`bs_p0`) and 53 (`input_B`). The exact certificate consumers of `q` are rows 11 (`bs_p0`), 13 (`bs_p2`), 15 (`bs_p4`), 19 (`sn2`), 54 (`wn2`) and comparison 1. No private scaled register is exposed as a comparison endpoint.

Under the literal hatted bindings, the three boundary values are padded_A=16A_pack+12, padded_B=16M_pack+10 and F3=16Z_pack+8. Their offsets matter. The component also retains q=16T and the complete truth-class/checksum machinery; a wrapper cannot infer that its native equation list is replaceable by a single norm constraint.

## 4. Optional raw-pack header, separate from the saved census

The verified private consumers permit a fresh seven-row header on already paid raw pack inputs:

    q=16T;
    scaled_A=16A_pack; padded_A=scaled_A+12;
    scaled_B=16M_pack; padded_B=scaled_B+10;
    scaled_Z=16Z_pack; F3=scaled_Z+8.

This is not the literal saved header. Hand algebra proves all four exit values q,padded_A,padded_B,F3 identical to the parent header after its hatted parameter bindings, over every commutative ring. The three altered private scaled values have no other consumers. Consequently every retained downstream value and comparison residual, and therefore the complete native sum of squares, is identical under that input substitution.

This header avoids three separate outer `pack+1` rows compared with first materializing all hatted ports and then retaining the original seven rows. It preserves the native positive relation by the conceptual positive graph Hhat=A_pack+1, Mhat=M_pack+1, Zhat=Z_pack+1. Its whole-wrapper saving still requires an actual source and full consumer audit; no universal bound or formal degree claim is made here. The saved census and source hashes above remain unchanged.

## 5. Execution and review limits

The accepted full native proof interface was read inertly. This task independently parsed the exact saved JSON and checked only row shapes, symbol availability, literal operations, comparison endpoints, dependencies, consumer lists, reachability and serialization hashes. Historical scientific test counters and degree assertions were not rerun or independently recomputed. The helper file was hashed as bytes only; it was not imported or executed.

No saved array was numerically or symbolically evaluated, and no degree was propagated. No repository or frozen predecessor file was changed. The fresh audit and receipt are under /tmp. The later complete wrapper still needs an independent whole-source topology/count/consumer review and the already specified projection proof at its exact ports.
