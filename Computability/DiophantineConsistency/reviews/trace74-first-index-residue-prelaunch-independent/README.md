# Independent scoped prelaunch review: first Pell index residue

**GO for one coordinated direct-pin author check** of source SHA-256 `5454d0e46d9e89800a96203ff244c23dae6dc2dab2737defa3587b52156fc9ce` and runner SHA-256 `c1f6dfcacf4c283ad1d008db4fa66336ef0aaae4b84cd6ed2d6318bc475d8efb`. No Lean was run in this review.

The source assumes the same model, positive beta and original 74 valuation, and actual 74 zero as the accepted Pell client. For `P=XY²` and `B=2*(P-1)+1`, P>0 gives `B+1=2P`. Using actual X=wq and Y=q³s, `q⁴` divides `B+1`. The inspected generic `residue_quotients` theorem gives `ycoord n B=n+q⁴*t` for the **same positive n** returned by the Pell theorem; the same ordinate `k=2*ycoord n B` then yields `k mod q⁴=(2n) mod q⁴`. This does not identify n with any rank or derive a mask guard.

Independent read-only preflight and all 13 actual report-policy controls (test SHA-256 `a82b5dfab4f8fb32164064218713218c52c01357c637c375692fcfdc03f9e292`) passed. The runner pins the parent Pell object/terminal, three root objects, direct congruence provider, source, Lean and Init; it uses the shared lock, bounded resources and exact named report policy. An initial preflight encountered a corrected temporary-path issue before Lean; the current preflight passes. Actual tool exit must be captured.

This is direct-pin evidence with inherited search-path shadowing and project/package/dynamic/transitive ancestry; it is not a fresh full-closure replay. No rank congruence or equality, repunit, population, fixed-port guard or iPRA endpoint is claimed.
