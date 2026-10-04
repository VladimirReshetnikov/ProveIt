# Positive charts for the LOAD and SWITCH edge hats

This packet emits three complete positive-integer coordinate charts of the frozen **1,679-gate, 146-witness** matrix source. They remove the SWITCH hat, the LOAD hat, or both, using equations already forced at every positive integer parent zero. The resulting actual-table counts are **1,674/145 witnesses**, **1,676/145 witnesses**, and **1,671/144 witnesses**. The respective exact degrees rise to **53,347**, **53,347**, and **71,107**.

These are witness/count versus degree tradeoffs on the stated parent. They do not incorporate the separate 1,624-gate coefficient improvement, the separate controller-flow circuit identity, or any removal of IDLE. The ordinary-input theorem and all retained positive witness coordinates are preserved. The established universal 84-operation bound is unchanged.

## 1. Pinned parent and complete arithmetic

The [fresh helper](matrix193_positive_controller_charts.py) reads the [composed source](matrix193_composed_output_scout.md) only as inert JSON/text. The [receipt](matrix193_positive_controller_charts.json) contains all six full arrays, including three diagnostic arrays, their complete free/witness lists, the map from every reached parent register, the removed hats and residuals, literal ledgers and exact pullback checks.

| Inert parent | SHA-256 |
|---|---|
| `matrix193_composed_output_scout.py` | `e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317` |
| `matrix193_composed_output_scout.json` | `a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37` |
| `matrix193_composed_output_scout.md` | `83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748` |

The initial recursive transformer is adapted from the new, unfrozen root controller-chart probe. This standalone helper adds source-pattern authentication, independent ring identities, full mapped-register checks, positive-domain proofs and exact degree checks. No frozen predecessor Python is imported or executed.

All fixed matrix/group data, the 99-edge actual controller, 340 selected-coordinate lanes, native kernel, fixed-program recipe and eight fixed coefficient ports are unchanged. Computed registers may be signed. Supplied witnesses remain strictly positive integers; ordinary input is x>=0, with the original positive-input language obtained by restricting x>0.

## 2. Two exact controller equations

Write

    b=B−1,
    E=edge_hat0−1, S=edge_hat1−1,
    u=population_quotient,
    J=sum_e(edge_hat_e−1), P=b*J+1.

The literal flow and population residuals of the parent are

    r_flow = (J−E−S)+P−B*(J−E) = 1+b*E−S,
    r_pop  = b*u−(E+b−x) = x+b*(u−1)−E.                (1)

The helper checks the actual raw-edge rows, paid b and P definitions, complete flow/population producer patterns, the total-hat-sum identity for J, and the two corresponding squared residual positions in the parent finalizer. An independent sparse polynomial expansion verifies both reductions in (1) over the integer polynomial ring. The simplifications do not assume a typed path, a bounded counter, positivity or a zero equation.

The three charts are:

| Chart | Computed formerly supplied hats | Residuals deleted after substitution |
|---|---|---|
| Flow | edge_hat1 = 2+b*E | r_flow |
| Population | E=x+b*(u−1); edge_hat0=E+1 | r_pop |
| Both | E=x+b*(u−1); edge_hat0=E+1; edge_hat1=2+b*E | both |

In the flow chart, E is still the paid raw value of the retained positive LOAD hat. Whenever a raw value is already computed by a chart, its later consumers reuse it. In particular the computed SWITCH raw value is S=1+b*E. These are actual paid arithmetic producers; neither expression is supplied as a free port.

After substitution the indicated residual polynomial is identically zero. Its producer, square and addition to the SOS can therefore be removed by ordinary exact circuit simplification. The helper rebuilds the complete output with constant folding and literal common-subexpression sharing, then checks every row and free port is live. Counts below are from those complete arrays.

## 3. Full all-ring pullback and positive zero equivalence

For a chart c let phi_c insert its computed hats into the parent coordinates. The complete polynomial satisfies

    F_c = F_parent composed with phi_c                 (2)

over every commutative ring. The small ring proof establishes the raw-edge simplifications and the zero substituted residuals first. A separate expression interner then checks every reached parent register and the complete output against the emitted chart. The proof is not a conclusion from evaluations or from discarding a comparison merely because it vanishes on some examples.

Now restrict to the valid fixed recipe and positive integer witnesses. Here B>1, b>=1, x>=0 and u>=1. Every retained edge hat is at least one. Thus in the flow chart E>=0 and the inserted SWITCH hat 2+b*E is at least two. In the population chart x+b*(u−1)>=0, so the inserted LOAD hat is at least one. The same inequalities hold in the joint chart. All inserted parent ports are positive before imposing any zero equation. Equation (2) therefore sends every positive chart zero to a positive parent zero, with every common supplied coordinate unchanged.

Conversely the parent finalizer has the form

    native_product * (1+sum residual_i²) − 1.

At an integer zero, both factors are integers and the SOS factor is a positive integer. Consequently the SOS factor and native product both equal one, and every residual equals zero. Equations (1) then force exactly the deleted hat values displayed in the table. Projecting away those hats yields a positive chart zero. The maps are inverse on these positive integer zero sets; for each fixed ordinary input they preserve every common supplied port, including all native witnesses, state/edge data, block/extraction witnesses, height/global slacks, terminal fields and population quotient.

No new native extension or larger height is needed to transfer a parent zero. The x=0 boundary is covered by the same inequalities. This is not a claim of equivalence of unrestricted positive-real zero sets: both the integer finalizer argument and u>=1 matter. Equation (2), by contrast, is an all-ring identity without those domain restrictions.

## 4. Degree of the changed packing scale

Count ordinary x and every remaining supplied witness as degree one; valid fixed program numerals have degree zero. Set

    N=L+m+4, l_max=maximal fixed selected-block length,
    s=degree(Q), d=N*s+1.

For the actual array N=472 and l_max=194; for the diagnostic N=18 and l_max=2. In a single chart J has degree two, so P=b*J+1 and Q=C*P have degree s=3. In the joint chart S=1+b*E has degree three and leads J, hence s=4. In every case the scale leader is nonzero on a valid fixed recipe.

The literal packing retains q=32*B*Q^N, giving degree(q)=d. The top range-history term in Z has degree d−s, so the padded native field F3=16Z+8 has that degree. The other packed native fields have their unchanged structural bounds: padded A has degree d and padded B has degree d−1. The controller and selection regions are strictly below the top range region; the finite gaps in the saved layouts remain sufficient after these substitutions.

The native variables therefore have degrees

    X: 3d−s,     Y: d+1,      c: d+2,
    a=Y(X+1): 4d−s+1,        H_mod=4a+3: 4d−s+1,
    Delta=a²+H_mod: 8d−2s+2.

Here X=(w+(q−1)F3)q, Y=(2*odd_half+1)q, k=eta+zeta and c=kY+eta, exactly as in the retained native source.

The main norm cannot be counted from the naive square degree. Its actual full expansion is

    (X+a*c+g*H_mod)²−(a²+H_mod)c²
      = X²+2Xac+2XgH_mod+2acgH_mod+g²H_mod²−H_mod*c².  (3)

The fresh checker derives (3) from the literal parent cone as a six-term sparse integer polynomial. The unique largest term is 2acgH_mod, of degree 9d−2s+5. Its leading coefficient is nonzero. The other six native factor degrees are similarly determined by their displayed leading products; no further cancellation of a largest term occurs.

| Native factor, in source order used by the degree audit | Exact degree |
|---|---:|
| First norm | 5d−s+4 |
| Main norm | 9d−2s+5 |
| Auxiliary norm | 6d+14 |
| Index factor | 4d−s+2 |
| Linear factor | 4d−s+2 |
| Strong factor | 8d−2s+4 |
| Global bound factor | s |

For example the first leader contains the independent nonzero linear form tau_gap−eta−zeta; the auxiliary leader is i²c⁶; the index and linear leaders come from −hXY and −2hXY; the strong leader comes from −Delta*f². The global sum still has degree one while P has degree s. These give nonzero factors on every valid fixed-program specialization. Their degree sum is

    36d−6s+31 = (36N−6)s+67.                         (4)

The population-only flow producers J−E and J−E−S have canceled leaders. Their exact identities are the sums of raw edges numbered at least one and at least two, respectively, so both have degree one. The checker authenticates the total-hat-sum formula and uses these exact identities when checking leading coefficients. This lower-degree controller cancellation does not alter (4).

## 5. Extraction degree and the population tie

For a block of length l, the high shift remains

    high=high_hat−T_half,
    T=Q^(l−1), T_half=(C/2)*P*Q^(l−2).

The right side of the extraction comparison contains the term −T*Q*T_half, of degree s(2l−1). All other right-side terms have lower degree. In the flow chart, every selector in a fixed block has degree one, strictly below degree(J)=2; in the joint chart every such selector has degree at most two, below degree(J)=3. Thus this high-shift term strictly leads the left side in those cases.

In the population chart, the X selectors still have degree one. The final Y selector is LOAD and has degree two, equal to degree(J). Its leader E_top equals J_top. If a0 is the first coefficient of the reversed coefficient word, the full extraction residual has leader

    D_top * J_top * Q_top^(2l−2) * (C*K/2−a0),         (5)

where B=K*D and Q_top=C*K*D_top*J_top. The fixed padding recipe gives C/2>|a0| for all four saved leading coefficients, verified directly by the helper; the valid integer K>=1 therefore implies C*K/2>|a0|. The bracket in (5) cannot vanish. This explicitly resolves the only new top-degree tie.

Thus a longest-block residual has exact degree s(2l_max−1) in every chart. Block, low/dot bound, history, population and any retained flow residual have degree at most this value. The real sum of squared residuals has exactly twice that degree. Combining with (4), the complete polynomial has exact degree

    (36N+4*l_max−8)*s+67.                             (6)

This yields 53,347 for either actual single chart, 71,107 jointly, and diagnostic degrees 2,011 and 2,659. The degree has increased under the nonlinear coordinate substitution; it is not inherited unchanged from the parent.

## 6. Literal ledgers and fresh evidence

| Complete layout | Chart | M | A | Total | Positive witnesses | Retained residuals | Exact degree |
|---|---|---:|---:|---:|---:|---:|---:|
| Diagnostic | Flow | 125 | 173 | 298 | 50 | 19 | 2,011 |
| Diagnostic | Population | 125 | 175 | 300 | 50 | 19 | 2,011 |
| Diagnostic | Both | 124 | 171 | 295 | 49 | 18 | 2,659 |
| Actual fixed table | Flow | 800 | 874 | 1,674 | 145 | 19 | 53,347 |
| Actual fixed table | Population | 800 | 876 | 1,676 | 145 | 19 | 53,347 |
| Actual fixed table | Both | 799 | 872 | 1,671 | 144 | 18 | 71,107 |

Every row and supplied port is live. Both exact control identities, all raw-hat substitutions and the whole final polynomial pullbacks are checked. Forty-eight fresh signed full-source comparisons over two prime fields verify every mapped parent value and output after inserting the computed hats. Half use the saved fixed binding and half vary all fixed ports. These are off-zero arithmetic checks, not claims of accepting trajectories.

The helper also performs twelve full leading-component checks, two per source. It uses independently expanded pure-Q polynomial identities, the six-term main-norm identity (3), and the two explicit controller-sum identities when a naive leading term cancels. It verifies the seven factor degrees and the full degree with nonzero leading coefficients. These finite checks corroborate the uniform degree proof above.

All three complete diagnostic specializations are densely expanded modulo 1,000,000,007. Their degrees and leading coefficients are respectively 2,011 / 351,921,786; 2,011 / 881,388,337; and 2,659 / 685,581,945. The full coefficient digests are saved. The large actual polynomials are not densely expanded. No giant accepting outer fixture or native Pell tuple is newly materialized.

Run from any working directory after installation:

```sh
controller_wip=/absolute/path/to/native-stream-queue
python3 "$controller_wip/matrix193_positive_controller_charts.py" \
  --root "$controller_wip" --expect "$controller_wip/matrix193_positive_controller_charts.json"
python3 -O "$controller_wip/matrix193_positive_controller_charts.py" \
  --root "$controller_wip" --expect "$controller_wip/matrix193_positive_controller_charts.json"
```

Generation uses `--write`; replay uses `--expect`. The parser rejects duplicate JSON keys, receipt equality is recursive and type-exact, and explicit proof guards remain active under optimized Python.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass for all six frozen arrays. No predecessor script was executed.
