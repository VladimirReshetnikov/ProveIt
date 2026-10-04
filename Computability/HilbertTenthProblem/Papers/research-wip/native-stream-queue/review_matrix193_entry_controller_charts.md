# Independent review of the entry-shared positive controller charts

**PASS; no requested correction.** I read the complete frozen author helper and proof, the original controller-chart helper and proof, and the relevant complete source receipts as inert data. The fresh [independent checker](review_matrix193_entry_controller_charts.py) and [receipt](review_matrix193_entry_controller_charts.json) verify the three emitted actual-table arrays. No predecessor or author Python was imported or executed in this review, and no repository file was changed.

The reviewed author files are [matrix193_entry_controller_charts.py](matrix193_entry_controller_charts.py), [its receipt](matrix193_entry_controller_charts.json), and [its proof](matrix193_entry_controller_charts.md), pinned respectively to:

* Python: `7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf`.
* JSON: `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571`.
* Markdown: `27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122`.

The checker also authenticates the nine frozen dependency files: the complete entry-flow1622 trio, composed1679 trio, and original positive-controller-chart trio. Their full hashes are recorded in the review receipt.

## Source and identity checks

The audit counts every row in all three new arrays, verifies unique names and topological order, and establishes output liveness of every paid row and supplied port. It obtains:

| Actual chart | Multiplications | Additions/subtractions | Total | Positive witnesses | Retained residuals | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Flow |790|829|1,619|145|19|53,347|
| Population |790|829|1,619|145|19|53,347|
| Both |789|827|1,616|144|18|71,107|

Thus all 4,854 emitted rows are covered. Each array has 137 integer literals. All 578 parent coefficient rows remain represented; the ordinary input, fixed coefficient interface, native witnesses, extraction coordinates and IDLE witness are retained.

I reconstructed the controller contracts directly from the parent rows. With `b=B−1`, raw LOAD/SWITCH words `E,S`, and positive quotient `u`, the residuals are `1+bE−S` and `bu−(E+b−x)`. The paid substitutions are `E=x+b(u−1)` when eliminating the LOAD hat and `S=1+bE` when eliminating the SWITCH hat; each eliminated hat is the corresponding raw word plus one.

The independent checker first derives these expressions without trusting the author map. It then checks the exact vanished-residual identities in a six-variable integer polynomial ring. Only the resulting raw-hat and zero-residual identities are used when interpreting the entire parent DAG. Every mapped parent symbol and the complete output agree. The checks explicitly include all six native inputs, all 63 native rows and all twenty residual positions, with exactly the stated residuals eliminated. The complete parent product/sum-of-squares finalizer is authenticated as well.

For degree transfer, an independent dense coefficient expansion proves the four word identities between entry-flow1622 and composed1679: two degree143 polynomials with 144 coefficients each and two degree193 polynomials with 194 coefficients each. Their paid Q expressions are checked identical. The expanded and reduced flow forms agree by a separate exact ring calculation. With these proved cuts, all 1,042 common paid parent registers, the native interface, all residuals and the complete outputs agree over every commutative ring.

I also rechecked the complete pullbacks of the three original actual charts from their frozen arrays. Their supplied interfaces and nonlinear missing-hat expressions coincide with those of the new charts. Consequently each new complete polynomial equals the corresponding original chart polynomial on the same variables. This transfers the original proof's exact degrees, including its main-norm cancellation and bounded-high leading-term argument. The formula is `17,760s+67`, with `s=3,3,4`. This review makes no new dense full-degree expansion claim.

## Positive integer equivalence and scope

For valid fixed numerals, `B>1`. At every allowed child tuple, `x≥0`, `u≥1`, and a retained LOAD hat is at least one. Hence every computed raw LOAD word is nonnegative and every reconstructed hat is positive. This holds before imposing zero equations and includes `x=0,u=1,E=0`.

At a parent integer zero, the unchanged finalizer has the form `N_native*(1+sum r_i²)−1=0`. Its positive integer second factor must equal one, so the deleted residuals vanish and uniquely recover the eliminated hats. Reconstruction and forgetting are inverse on the complete positive integer zero sets. All common supplied ports retain their values. The author correctly avoids a positive-real equivalence claim and does not remove IDLE.

The finite boundary checks cover 81 elementary coordinate cases per chart, including zero input and quotient one. These 243 cases corroborate only the displayed arithmetic maps; they are not full native zeros or authentic compiler histories. No diagnostic array or giant trajectory was emitted or replayed by this review. The language conclusion uses the unchanged valid fixed-program recipe and inherited simulation theorem; arbitrary assignments to coefficient ports receive only the polynomial-identity conclusion. The established universal84 bound is unchanged.

Fresh generation and exact normal and optimized replays of the independent checker from `/` passed. The final review helper and receipt hashes are:

* Python: `a9f2570f27376c9f64a8074871f05da2d8b7ef56d79aa37c50da0bcd6957be5d`.
* JSON: `bd0c48ad299c5b7bf374b4fdbe15af5d82eda1aa0704a884b62f01e8368a3069`.

After installation, with all authenticated files in one directory:

```sh
review_wip=/absolute/path/to/native-stream-queue
python3 "$review_wip/review_matrix193_entry_controller_charts.py" \
  --root "$review_wip" --expect "$review_wip/review_matrix193_entry_controller_charts.json"
python3 -O "$review_wip/review_matrix193_entry_controller_charts.py" \
  --root "$review_wip" --expect "$review_wip/review_matrix193_entry_controller_charts.json"
```

`--author-root` optionally supplies a separate directory for the author trio; it defaults to `--root`. Duplicate keys, nonfinite JSON, pin mismatches and type-sensitive receipt differences are rejected without reliance on assertions.
