# Bounded independent endpoint-penalty review

PASS for source `7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c` and receipt `10cbe0a62be35c03da5e9902e88c55b457c28b3c7295026fb6f33472dbdc82c8`. I read the complete 203-line emitter/checker and companion note. No change requested. This is a bounded review of the natural theorem and seven saved actual certificates, not a rerun of all 80 author pairs.

The proof is sound. Every retained square and inactive mass product is nonnegative on the full natural orthant. The retained one-hot rows force exactly one natural selector to be one at each step. Therefore an unweighted sum of selectors of forbidden source or target branches vanishes exactly when the original weighted state-code residual vanishes; distinct state codes suffice, and neither extremal initial nor extremal halt codes are needed. This proves identity of complete supplied-natural zero tuples, retaining every witness and all endpoints. For h=0 no row changes. For B=0 at positive horizon the constant-one one-hot row prevents all zeros. The source does not silently remove the one-hot row just because an endpoint square is the same polynomial: its loop retains rows by label, and shared squaring gates remain live when required.

The full correction is exactly `K0+Kh-C0^2-Ch^2`; the polynomial is changed away from zero. The natural theorem does not extend to signed selector tuples or the rational simplex. The companion gives appropriately distinguished complete signed and local rational examples. The warning about substituting an implicit selector is necessary: the substituted linear penalty need no longer be nonnegative, so the theorem cannot be composed without a fresh barrier proof.

My separate checker imports no author code. It reads the frozen receipt, derives the old complete mass polynomial directly from each actual exported affine square/product, computes endpoint masks from the literal branch source/target labels, and expands every gate in all 14 saved old/new circuit pairs. Exact coefficients match; every charged node is live; all 1,742 paid gates are counted; each final polynomial has degree two and coefficient one on `T^2`; the paid `N0=x+1` port and unchanged coordinate/witness lists are checked. This independently verifies the saved worked counts 56→51 for both native and compact-clean INC2;DEC2, 107→100 and105→98 for the respective three-increment chains,30→29 for zero3,5→5 for the empty h0 source, and83→76 for the interior-code fixture.

The complete source read confirms the baseline path emits the parent's same whole schedule, both inactive-sum options are charged, and the new linear mask joins the paid final sum. The author note limits minima to those actual schedules and gives no universal B/h saving formula. Its explicit raw-x/native-y,T or compact-clean-T interface remains a fresh-certificate prototype boundary, not a hostile schema validator. The external horizon and ordinary-counter input decoding obligations remain explicit.

Fresh saved-receipt replay passed:

```sh
python review_three_mass_endpoint_penalties.py \
  --source three_mass_endpoint_penalties.py \
  --receipt three_mass_endpoint_penalties.json \
  --output /tmp/endpoint-penalty-review.json \
  --expect review_three_mass_endpoint_penalties.json
```

The independent helper authenticates source and receipt before reading the schedules. Its finite expansions substantiate exactly the saved 14 pairs; the preceding nonnegativity/one-hot argument proves the general natural-zero statement.
