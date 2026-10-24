# Execution safety review

Before the integrated replay, the selected builders, checkers and imported local
modules were inspected as source text, including import paths, dynamic imports,
formula evaluation, file writes and command entry points. `CODE_REVIEW.json`
records the exact inspected execution closure and hashes. This is a bounded
source review, not a formal security certification.

No network client, credential access, shell command, package install, OS-setting
change, or deletion outside isolated temporary copies was found in this
execution closure. File writes in component scripts are limited to their own
output/receipt paths. The root runner writes evidence outside the release and invokes these programs only in fresh
copies, using argument arrays and `shell=False` (the subprocess default).
Negative-control utilities use Python-managed temporary directories.

Several compact formula builders/audits use `eval` on locally fixed arithmetic
expressions with empty builtins and explicitly supplied polynomial symbols.
Those expressions, and the twelve-variable specification input, were inspected
as arithmetic expressions. The root manifest pins these exact inputs before
execution; untrusted changed input must not be accepted by simply resealing.
Dynamic imports are restricted to the explicitly included and inspected helper
or numeral-recipe files. SymPy is the sole third-party runtime dependency.

No inherited external code under the retained prior release, baseline evidence,
or alternative proof-intake trees is executed. Historical scripts may contain
other operations and are outside this execution review. Their old receipts are
retained provenance, not new safety or replay claims.

TeX and shell render scripts are not invoked by `reproduce.py`. PDF compilation
and visual QA have their own separately reported scope.

The twelve-variable specification has 53 formula expressions. Their ASTs were
checked to contain only integer literals, names, scalar addition/subtraction,
multiplication, fixed powers, and unary signs; no calls or attribute access.
The deterministic ZIP builder reads the sealed tree and writes only to the
explicit external destination and temporary paths within its parent.
