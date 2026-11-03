# Checked all-ring center substitution

`Trace73CenterV2.lean` defines the proposed centered output from the checked `TenPositiveTrace75.regs` and updates witness slot 7 from `n` to `n + V² B`. The theorem `Trace73Center.substitution` proves, over any commutative ring, that the parent 75 expression at this updated valuation equals the centered expression at the original valuation. `centerZ_shift` gives the underlying center-register equality. Both report only `propext` as an axiom in the accepted `observations/attempt02/`.

The accepted Lean invocation returned exit 0, with empty stderr and no warnings or errors. Its output object is `/tmp/trace73-center-r4z617bq/Trace73CenterV2.olean`, SHA-256 `fe3d39ec315888286a4d9d5ec2763badf338dc11bf141c0e19fa58f575de1e5a`; the exact source, runner, Lean executable and direct 75 provider pins appear in the receipt. `observations/attempt01/` retains the initial failed source and diagnostic. The runner uses the selected parent object and package provider; their transitive project, package and dynamic ancestry is inherited, not independently replayed here.

The theorem is an identity of Lean ring expressions. It does not formally parse or bind `candidate.json`, and it does not establish positivity of either transformed witness, equivalence of positive graph zeros, or an iPRA result for the 73-row candidate.
