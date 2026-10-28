# Independent audit of the final four-plan composition

The local proof is valid under the inherited rectangular backend and weighted pair-entropy interfaces. For q=4 plans, `min_j F_j ≤(1/4)sum_jF_j`; taking the maxima over their fixed support sets gives coefficient vector `(v1+v2+v3+v4)/(4L)`. Each undirected coordinate is repeated on two directed orientations. Thus the squared local constant is exactly `2Q/(16r²L²)`, **not** the old denominator9 or a missing factor2.

The four r=9 plans listed in `four_plan_portfolio_new.md` are the affine-plane parallel classes; every unordered vertex pair is co-blocked exactly once. This fact motivates the menu but is not used as a substitute for its whole-operation certificate. At r=13, the appended plan is exactly the permutation `5x+3 mod13` split5,4,4. Ordered block splitting matters and is included.

Author-written `tree_checks/audit_four_plan.py` reconstructs every operation by subset bit masks (rather than the primary verifier's vertex-label map), forms all nine rectangular linear supports, deduplicates and independently exhausts all support quadruples. Its enumeration order permutes the primary plan order to `(0,2,1,3)`; a maximizing tuple is checked directly coordinate by coordinate. Exact Gram products are only an arithmetic acceleration of squared Euclidean norm, not a relaxation. The certificate counts are57^4=10,556,001 and89^4=62,742,241. Expected maxima and coefficients are:

| r | Q | b_r² |
|---|---:|---|
|9|405850918811760|563681831683/1764000000000|
|13|895372728026656|27980397750833/82810000000000|

All masks include the output-size branch; consequently the selected operation-cost bound controls each actual stored input/output table, including singleton caches. Recursive singleton evaluation is **not** included for free: it remains separately charged with alpha_r=√(2(r−1))/r.

With the frozen generic fractions f0=1577/100000, f1=2813/250000, f2=1433/300000 and r7 geometric tail ratio4/9, the full recurrence has:

- root local coefficient28.853020941407...;
- first cached prefix plus depth1 local coefficient30.490561591676...;
- entire paid cached path coefficient30.491276185937....

The last one dominates, narrowly but strictly. Reporting only the second would understate the proved upper envelope. Tail factor alpha7/(1−3/7)=√3/2 exceeds the retained r7 local constant; finite leaves stay lower order. Independent rational square-root and Machin/ln2 intervals verify the maximum, root-space dominance, safe coefficients30.492/28.854, and unchanged exact packing gates. No recursion-cost or space-product omission was found.

## Final low-degree composition

For degree≤ceil(s^(1/12)), use the final r13 four-plan local coefficient at every depth and retain total taper A=119/1000, but set **q=24/125**. Then f0=A(1−q)=12019/125000, gamma=(2/13)/√q and:

`C_local=κ b13/√f0=12.015609290141210...`,

`C_children=κ alpha13/[√f0(1−gamma)]=12.004596197275639...`.

Therefore **12.016 time and space** is a safe eventual certificate. Keeping the former q=181/1000 while merely lowering b13 would fail to obtain this root-local bound, because the unchanged paid-child series would dominate. The strict total-capacity certificate338^119<2^1000, degree growth, precision buffer and noncircular depth argument from `tree_review.md` remain unchanged. In particular q>1/6 and2/13<1/6 close the H=s/λ^(2/3) stopping argument. No additional plan or schedule search was performed for this audit.

`tree_checks/check_schedule_combinations.py` certifies the final local-vs-child comparison and safe12.016 bound with exact rational enclosures; normal and optimized JSON are identical. The independent four-plan receipts are `tree_checks/four_plan_audit{,_optimized}.json`.

All programs used here were authored in this iteration; no incoming archive program was executed. These checks audit the new finite algebra/recurrence composition, not the entire upstream ETH theorem or a proof-assistant development. No smaller logarithmic order or practical SAT speedup follows from the numerical certificates alone.
