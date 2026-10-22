Compact unrestricted-integer low-degree portfolio
Pinned source: VladimirReshetnikov/ProveIt at f0ae4e0991ca44a7bb4e5671d42e33d775e48035

Primary artifacts:
  integer54_quartic.json: 54 integer variables; exact degree 4; 31 squared residuals.
  integer45_degree6.json: 45 integer variables; exact degree 6; 22 squared residuals.
  integer39_degree8.json: 39 integer variables; exact degree 8; 16 squared residuals.

All variables are unrestricted integers. The four fixed coefficients are the
complete T4-4094 tuple in ../coefficients/COEFFICIENTS.json.
ORIGINAL_COEFFICIENTS.json is retained solely as historical source evidence.
The polynomial is precisely the sum of the squares of the listed residuals.
The quartic also includes its full expanded sparse polynomial.

Replay:
  python build_domains.py
  python build_tradeoffs.py

Proof: DOMAIN_REDUCTION_PROOF.md, including the low-degree frontier appendix.
Audits: DOMAIN_CHECKS.json and TRADEOFF_CHECKS.json.
Exact-degree certificates are present in the proof and artifact metadata.

The constructions have a zero exactly when the encoded K215 blank computation
halts, equivalently when there is a finite syntactic ZFC refutation. Their
absence of integer zeros expresses Con(ZFC). This is an ordinary mathematical
reduction using pinned Pell/compiler results, not a new kernel-checked proof
and not a claim of global minimality. Fixed numerals have exact finite recipes and complete unsigned binary
expansions in ../coefficients/expanded/. No proof of consistency or inconsistency is
claimed.

Optional finite-sweep variants:
  integer37_degree10.json, integer35_degree12.json, integer34_degree16.json.
The direct integer46_octic.json is dominated in variable count by the primary
39-variable octic and is retained only as an intermediate exact identity check.

Source notices are retained in LICENSE.ProveIt. Vendored source documents and
code carry the precise mathematical dependencies. The root verifier never
executes any vendored Python source.
