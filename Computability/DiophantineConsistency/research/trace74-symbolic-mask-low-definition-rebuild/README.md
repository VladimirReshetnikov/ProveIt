# LowNat definition isolation diagnostic

The [prelaunch review](../../reviews/trace74-mask-isolation-prelaunch-independent/README.md) approved one run. Attempt01 completed with actual outer exit 0 and child status PASS. The [child result](observations/attempt01/result.json) SHA-256 is `7399ca5b440dc883c08c0738aba4b7c681af9bb648322930e646da4f0f6d2bde`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `eb9cb9d84d870447abbefc9032b1e457e3d9bbe485f277bc8b72b22458643b15`; object SHA-256 is `ea2cc1c7962d8e1190c8944df85207c9d56a5d6c3e9dca872e1f7ae75166064b`. The [independent result audit](../../reviews/trace74-low-definition-result-independent/README.md) passed.

This theorem exposes the retained `CompactSymbolicPorts.lowNat` as the unexpanded `Nat.ofDigits` recipe. It does not establish the concrete mask cover or graph guard. Capture-relative provider and package ancestry limitations remain.
