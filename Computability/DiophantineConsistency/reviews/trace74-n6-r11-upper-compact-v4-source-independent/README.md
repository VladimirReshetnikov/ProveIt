# Independent factual v3 audit and v4 source review

V3 overall FAIL; author reports actual outer session 70516 exit 1/reaped. Terminal `ea7a5a60653e3a88c073978b58257989c4584ec900a22a7a64045792027af634`; all eight input pins, logs and base object independently rehashed. Base Lean exit 0, output `960d185dddc1b1a7494c8292e2423e4d38c0536ef43bd37df4ae87705f325411`; upper Lean exit 1/no object, additive orientation mismatch and consequent sorryAx report excluded.

V4 source-only PASS: base `7923fcd2ecfb72f02f56b25bb6f4236c639ab059fb25fa04fcde5b1acaa838fd`, upper `cf5a56e6ac6ac2ce16320d4080ef863bdb0c9fa2cd62feeb3db25684b2bd986b`. Exact source diff replaces the `simpa [add_comm]` over `add_le_add_left` with `add_le_add_right` for the displayed orientation; no theorem/math changes. Lean elaboration untested. Generic scalar upper only, no graph/guard claim.
