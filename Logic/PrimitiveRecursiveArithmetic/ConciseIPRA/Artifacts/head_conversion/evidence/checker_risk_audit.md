# Independent final risk audit of the six-rule checker

Reviewed `output/ipra_head_conversion_2026-11-12/code/head_checker.py` and `verify_head.py`. The reviewed checker hash and executed targeted checks are recorded in `checker_risk_checks.json`.

## Conclusion

**No soundness defect found.** The implementation agrees with the reviewed six-rule raw-hint presentation. No code change to the checker is recommended by this audit.

## Specific high-risk boundaries reviewed

1. **Input sorts and scope.** `walk` distinguishes terms from formulas at every constructor; `raw` requires an actual integer variable index in range, excluding booleans and negative indices. Iterator bodies raise the de Bruijn scope by one; Q and D matrices raise it by one and two. Public contexts and goals are validated before normalization and are required to be canonical.

2. **Raw hints before erasure.** Every used VS replacement and minor hint is checked in the current scope before `instance` or `normal` can erase a subtree. QE targets and DI witnesses are similarly checked. QE/DE matrices are validated at their precise extended scope and required to be canonical. In VS, fixing the output-side raw hint to the stored left endpoint loses no expressive power because that side is never substituted into.

3. **Substitution.** `sub` leaves indices below the selected variable untouched, shifts the replacement under each local binder, and subtracts `drop` only above the removed index. VS uses `drop=0`; QE removes index 0; DI removes its witness at index 1 using a shifted raw witness and later replaces the remaining index 0 by its successor without dropping it. These uses match the mathematical rules.

4. **Fresh eigenvariables.** DE shifts the target and every retained context member, reserving index 0 exclusively for the fresh witness. Its added Q matrix has the correct two-layer binding. DI likewise shifts the old context; case mode shifts the zero instance, whereas progress mode retains the index-0 equation as its induction assumption. The raw witness is validated before entering the fresh scope. The mode test on the substituted matrix's root is equivalent to testing the original matrix's root, since substitution and normalization do not change Eq/Q/D constructors.

5. **Canonical intermediate formulas.** Every recursive goal is built from already canonical components or is the result of `normal`. The normalizer leaves successor arguments and neutral iterator seed/body arguments untouched exactly as specified. Recomputing a formula after substitution is endpoint normalization, not normalization of the substitution range.

6. **Failure behavior.** Validation uses explicit exceptions, not Python assertions, so optimized execution does not disable checks. Unknown constructor tags, malformed arities, incorrect sorts, invalid indices, and malformed JSON fail without reaching the success output.

## Targeted negative checks

The original erasure rejection fixtures included the malformed term inside the public goal, so they could fail before exercising raw-hint validation. This was a test-quality gap, not a checker defect. The parent repaired it by adding four cases with fully valid contexts and goals:

* Context `v1=v2`, goal `v2=v1`, VS source `v0`, and replacement hint `I(0,v0;body)` with an out-of-scope or ill-sorted erased body.
* The same context and goal, valid replacement `v0`, and minor hint `I(0,v1;body)` with an out-of-scope or ill-sorted erased body.

All four are rejected. Removing the selected replacement validation admits both malformed replacement cases. Removing the selected minor validation admits the out-of-scope minor case; its ill-sorted companion remains rejected by the independent sort traversal inside substitution. This confirms the tests reach the intended boundary and explains the overlapping sort protection.

One focused eigenvariable-leak attempt was independently executed. Let

`B(x,y) := C(y,0,x)=C(y,0,1)`.

At one outer parameter, introduce `D B` using witness 1, then try to prove the false open consequence `outer_parameter=1` by opening D and reading its row at 1. The row gives `fresh_witness=1`; the checker correctly requires the shifted outer target and rejects. A temporary in-memory mutant deleting exactly the DE target shift accepts this false consequence. The production checker was never modified.

## Accepted proof-leaf convention

When the requested formula is already a hypothesis or is reflexive, `prove` succeeds immediately and ignores the supplied proof payload. Thus syntactically irrelevant garbage below an already successful leaf may be ignored. This does not permit a false formula or unvalidated public goal: it is the certificate protocol's implicit Hyp/Refl convention. Claims about hint validation should refer to hints actually used by an inference, rather than claiming that every byte of an ignored proof payload is parsed.

## Limits

The audit covers implementation soundness risks and focused regression evidence. It is not a machine-checked universal correctness theorem. Resource exhaustion can reject very large valid inputs; no termination claim is inferred from the finite test set. The unbounded normalization and equivalence arguments are the written proofs supplied separately.
