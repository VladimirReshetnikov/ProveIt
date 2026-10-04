# Remove the optional IDLE witness and cancel its controller terms

Four complete actual-table sources now use **1,618 / 1,615 / 1,615 / 1,612 operations** and **145 / 144 / 144 / 143 positive witnesses**. They specialize the [entry-flow1622 source](matrix193_entry_flow_scout.md) and its three [positive controller charts](matrix193_entry_controller_charts.md) at `edge_hat98=1`. Their respective exact degrees remain **35,587 / 53,347 / 53,347 / 71,107**.

Each source removes one positive witness and four paid operations, one multiplication and three additions/subtractions. This packet does not yet incorporate the separate577-row affine coefficient successor. The established universal84 bound is unchanged.

The [fresh helper](matrix193_idle_free_scout.py) emits all four complete arrays in its [receipt](matrix193_idle_free_scout.json). It reads frozen dependencies only as bytes, text or JSON and executes or imports none of their programs. There is no new diagnostic array or giant accepting/native fixture.

## 1. What the IDLE restriction means

The actual fixed controller has99 edges. Edge0 is LOAD in state0, edge1 is SWITCH from state0 to state1, edges2 through97 are the96 paired TILEs in state1, and edge98 is the identity IDLE loop in state1. Accepted paths have the form LOAD* SWITCH followed by TILEs and optional IDLEs, with terminal matrix-row equality. The frozen [atomic construction](matrix193_atomic_context_packing.md), Sections1 and6, proves this interface and positive completeness with zero or more optional IDLEs.

The raw IDLE indicator is `edge_hat98−1`. Setting its positive hat to1 forces that indicator to zero. This is a restriction of the parent's positive zero set. The construction below proves the same **ordinary-input projection**, using fresh witnesses in the reverse direction. It does not claim a bijection preserving all common witness coordinates.

The instruction slots, physical lane positions, fixed power schedules and all matrix words remain unchanged. In particular the old IDLE slot is zero; the controller continues to occupy its fixed128-lane region. The packet does not renumber the other98 edges or silently shorten any packing exponent.

## 2. Four paid gates disappear

Use Q for the already paid packing scale. On the uncharted entry-flow parent, the relevant literal rows are

    r104 = r103 + edge_hat98;
    J = r105 = r104 − 99;
    r568 = edge_hat98 * Q;
    r569 = r568 + edge_hat97;
    r570 = r569 * Q;
    ...
    r763 = sum_(e=0)^98 edge_hat_e * Q^e;
    r773 = r772 + r187;
    controller_word = r774 = r763 − r773.

Here `r103=sum_(e=0)^97 edge_hat_e`, `r772=1+Q+...+Q^97`, and `r187=Q^98`. The fresh helper checks the actual parent rows and expands the complete repunit, rather than trusting these register names. In a controller chart it uses that chart's authenticated parent-register map to locate the same rows, including the computed LOAD or SWITCH hat where appropriate.

Under `edge_hat98=1`, the edge sum becomes

    J = sum_(e=0)^97 edge_hat_e − 98.

Remove r104 and directly compute `r105=r103−98`. For the controller word, the added high term Q^98 cancels the same term in the repunit. Start the Horner word at edge_hat97, remove r568 and r569, and change r570 to `edge_hat97*Q`. Remove r773 and subtract the already paid r772 at the final controller-word cut. The result is exactly

    sum_(e=0)^97 (edge_hat_e−1)*Q^e.                 (1)

The four deleted rows cost1M+3A. Three retained rows have changed operands: J, the first remaining Horner multiplication and the final controller subtraction. All other instructions remain literal. The transformed source is checked for complete topology and liveness; no supposedly saved row has a surviving consumer.

The entire Horner region is private except for its one final controller-word consumer. Its intermediate values change, which is expected. The proof does not claim that these internal prefix words equal their old values after specialization. Every other retained paid expression does agree.

## 3. Full polynomial identity

Treat all98 remaining hats and Q as independent formal variables. A fresh integer-polynomial expansion checks both parent cuts at IDLE=1 and both emitted child cuts. It verifies the full edge sum and all196 nonzero monomials in (1), as well as the complete paid R98 repunit. Computed LOAD/SWITCH hats can be substituted into these identities afterwards, because the identities hold for arbitrary values of their formal ports.

An independent expression interpretation then compares the entire parent and child DAGs. The old IDLE port is the integer1. Only the two just-proved cuts are normalized: their formal tokens include the actual remaining-hat values and, for the controller word, the actual Q value. Thus equality of cut names alone is not used to assume equality of their inputs. Every other operation is interpreted literally.

The complete output identity is

    F_child(all remaining supplied values)
      = F_parent(all those values, edge_hat98=1)     (2)

over every commutative ring. Every common non-Horner expression is checked, including all six native inputs, the complete63-row native block and all twenty original residual positions. Positions already eliminated by a controller chart remain their proved literal zero. The full finalizer is retained from the parent. The source also checks that all retained non-Horner rows outside the two cuts are literal.

## 4. Ordinary-input completeness without time padding

Fix any valid inherited program recipe and input x≥0. Inserting the positive integer1 at the removed IDLE port maps every positive child tuple to a positive parent tuple. Equation(2) proves soundness immediately from the parent's ordinary-input theorem.

For the reverse direction, take an accepted input. The fixed matrix language has an accepted finite TILE word. Use exactly x LOADs, the compulsory SWITCH, and that TILE word, with no IDLEs. Removing identity loops preserves the state endpoints, terminal matrix products and LOAD count. The length is

    t=x+1+number_of_TILEs >= 1.

Choose a sufficiently large dyadic D above x+Hfix and all absolute coordinates of this finite trajectory, including its endpoint, plus one. Set B=K*D and use the unchanged fixed packing and coefficient recipe. The atomic completeness construction builds all edge/history/selection words and fresh positive native witnesses at exactly the resulting q. The IDLE raw word is zero, so its hat is1.

There is no lower bound on t that requires an IDLE. The global-slack estimate in the atomic proof is

    bound_global >= ((K−16)D+7)*J − ell + 2 > 0,

where K≥32, ell=340, D>Hfix≥ell, and J≥1 follows from the mandatory SWITCH. At most four selection lanes are active per cell. Each absent selection still has positive hat1. The LOAD population quotient

    u=1+sum_(LOAD cells j) (B^j−1)/(B−1)

is a positive integer. The native converse is available at the constructed exact q; it does not demand an independently supplied duration or extra IDLE padding.

The later packed-block, balanced-extraction and bounded-high constructions apply to this freshly built typed history. Their ordinary-input completeness maps preserve the edge hats. The bounded-high change supplies its positive high hats by the strict whole-tail bound, so zero IDLE activity causes no boundary failure. The exact coefficient/flow rewrites preserve every supplied coordinate. Finally, applying any of the reviewed LOAD/SWITCH coordinate charts preserves the still supplied IDLE hat1 and gives the appropriate current parent zero. Projecting away that IDLE hat gives a child zero by(2).

The zero-input boundary is covered. If the fixed language accepts an empty TILE word at x=0, the corresponding trajectory is SWITCH alone, still one cell; the LOAD raw word is0 and u=1. This is a conditional boundary construction, not an assertion that every program accepts zero input.

Deleting IDLEs generally changes the radix positions of later history digits. The reverse construction may also choose a new height and new native witnesses. The theorem is therefore equality of ordinary-input projections. No equivalence of arbitrary retained witness tuples or unrestricted positive-real zeros is asserted.

## 5. Uniform exact degree after specialization

Fix the valid program numerals and give degree one to the remaining ordinary input and witnesses. Let K be the fixed radix multiplier, D_top the degree-one leading form of D, and u the population quotient. The leading forms of J after removing IDLE are

| Parent variant | J_top | s=degree(Q) |
|---|---|---:|
| No controller chart | sum_(e=0)^97 edge_hat_e |2|
| Flow chart | K*D_top*edge_hat0 |3|
| Population chart | K*D_top*u |3|
| Both charts | K²*D_top²*u |4|

Each is nonzero. The omission of one degree-one summand cannot remove the larger J leader in any of the three nonlinear charts. The packing layout still has N=340+128+4=472 and longest fixed block length194. Write d=472s+1. Then q has degree d, F3 has degree d−s, and the seven native factor degrees remain

    5d−s+4, 9d−2s+5, 6d+14,
    4d−s+2, 4d−s+2, 8d−2s+4, s.

Their sum is36d−6s+31. The helper independently expands the actual main norm at its five cuts. Its canceled square terms leave six terms, with unique highest term2acgH. The other native leaders retain the same independent native factors as in the pinned degree proofs: the first norm contains tau_gap−eta−zeta, the auxiliary leader is i²c⁶, the index and linear leaders contain −hXY and −2hXY, and the strong leader contains −Delta*f². The global sum contains independent selected-output hats and stays degree one. These leaders survive every valid fixed-program specialization.

For the outer extraction residuals, the uncharted case retains the independent SWITCH-hat term in the tied bracket

    (C*K/2)*J_top − a0*S_last,top.

The fixed X/Y blocks contain neither SWITCH nor IDLE, so the coefficient of edge_hat1 in this bracket is nonzero. Removing IDLE therefore cannot destroy the old baseline degree proof. In the flow and joint charts, the bounded-high shift still strictly leads the selector term. The population chart has the same final LOAD tie as before, resolved by C*K/2−a0≠0; the fixed padding has C/2>|a0| and K≥1. The actual two leading Y coefficients remain −490 and271.

A longest-block residual consequently has degree387s. All other outer residuals have degree at most that value, and the real sum of their squares has exact degree774s. The complete output therefore has degree

    36d−6s+31 + 774s = 17,760s+67.                 (3)

This yields35,587 /53,347 /53,347 /71,107. Degree is not inferred merely from substituting a constant into a parent of that degree; the surviving leaders establish equality.

## 6. Full counts and evidence

| IDLE-free parent variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |790|828|1,618|145|35,587|
| Flow |789|826|1,615|144|53,347|
| Population |789|826|1,615|144|53,347|
| Both |788|824|1,612|143|71,107|

Every row and supplied port is live in all four full arrays. The four literal savings are checked against each parent; none is inferred by adding separate headline savings. The eight fixed coefficient ports and all selected-coordinate lanes remain in the interface. The same578-row coefficient component is retained; the separate577-row affine successor is outside this packet.

Thirty-two fresh signed full-source comparisons over two prime fields corroborate(2), checking every common non-Horner register as well as the output. Half use the saved illustrative fixed coefficients; half vary all supplied ports. Eight fresh leading-component checks, two per source, verify all native factor degrees and nonzero complete leaders modulo1,000,000,007. Exact pure-Q expansions and the six-term main-norm identity justify their cancellation overrides. These finite checks supplement the uniform proof, not replace it.

No frozen predecessor program is run or imported. No diagnostic source, dense giant polynomial, accepting outer trajectory or native Pell tuple is newly materialized. The universal84 construction remains the established overall bound.

## Replay and inert dependencies

After installation, run the new helper normally or with optimized Python:

```sh
idle_wip=/absolute/path/to/native-stream-queue
python3 "$idle_wip/matrix193_idle_free_scout.py" \
  --root "$idle_wip" --expect "$idle_wip/matrix193_idle_free_scout.json"
python3 -O "$idle_wip/matrix193_idle_free_scout.py" \
  --root "$idle_wip" --expect "$idle_wip/matrix193_idle_free_scout.json"
```

Generation uses `--write FILE`. Duplicate keys and nonfinite JSON are rejected; recursive type-exact receipt equality and explicit proof guards remain active under `-O`.

| Inert dependency | SHA-256 |
|---|---|
| matrix193_entry_flow_scout.py | `0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf` |
| matrix193_entry_flow_scout.json | `321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da` |
| matrix193_entry_flow_scout.md | `5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2` |
| matrix193_entry_controller_charts.py | `7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf` |
| matrix193_entry_controller_charts.json | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |
| matrix193_entry_controller_charts.md | `27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122` |
| matrix193_atomic_context_packing.py | `18ed65a37a471a17b31245b237b7e3b987c4cef58fcbd3c9dfb4b6d0c67daa32` |
| matrix193_atomic_context_packing.json | `7f9f9614f3862d08fa2645a5944a4567f4f268e4e93a57c5dec6e59d5a9fe8c9` |
| matrix193_atomic_context_packing.md | `b19f3a7188eac22055323ecc277522e18d68f0818c6f5d2da3a05ceea94262ca` |
| matrix193_positive_controller_charts.md | `e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c` |
| matrix193_bounded_high_output.md | `7f5a5bab9bff8518881a16a7c9d32916ce4ca1ff9dcbaa18f7fab7d452da654c` |
| matrix193_balanced_output_scout.md | `cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde` |

New helper SHA-256: `33e6c22b35e6fd2c8735380f04433652686b0da20053c5446b139e8881f9ed94`.

New receipt SHA-256: `857f5af683abb1c27cba6335fd45cadbd0afc7f9c630bf312a27ea4c98aa23b7`.
