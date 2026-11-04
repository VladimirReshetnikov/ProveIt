# Radix-and-index isolation diagnostic

The [independent prelaunch review](../../reviews/trace74-radix-indices-prelaunch-independent/README.md) approved one run. Attempt01 completed with actual outer exit 0 and child status PASS. The [child result](observations/attempt01/result.json) SHA-256 is `da19b3a409b5bcf144e979d1ac2ecd3e7988aae934b49d9472484cb8260c27bf`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `fe5f41a6fc9d0351af873eff58c8bd53174b97e54d1ad14c11bb592f03f6213a`; the output object SHA-256 is `0e0bf76abde32655ef1c9b69ad5672b6723e37e205744504020442ff51259785`. The [independent result audit](../../reviews/trace74-radix-indices-result-independent/README.md) passed.

This checks the low-plus-defect identity with base `2^67` and indices 3297, 8807 and 1063, while support remains symbolic under an explicit range bound. It does not establish the concrete mask cover or graph guard. Capture-relative provider and package ancestry limitations remain.
