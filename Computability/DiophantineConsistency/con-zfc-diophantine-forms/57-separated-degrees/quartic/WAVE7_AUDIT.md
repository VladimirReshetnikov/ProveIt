# Wave-7 baseline audit

Repository pin: `4b4349064a750ba6347293b55874a7f92abdd0db`.
All eight ZIP files in `docs/incoming` were inspected and extracted under
`audit_wave7/`. The following are their declared exact results; the audit
read their README/proof boundaries but did not rerun every release verifier.

| Archive | Nine positive degree / ops | Ten integer degree / ops | Other principal results |
|---|---:|---:|---|
| `ConZFC_Sparse_Support_2026-10-23.zip` | 25,936,016 / 651; 23,878,392 / 670 | 71,151,176 / 662; 65,506,504 / 675 | 15 positive, degree44 / 75 or76 ops |
| `ConZFC_Support_Sensitive_2026-10-23.zip` | 30,947,584 / 651 | 56,593,864 / 653 | 11 positive degree954 /115; shifted system952 /110;14 positive degree56 /79 |
| `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` | 7,344,328 /738;12,023,320 /734 | 21,111,400 /659 | 13 integer Jones-only57,866,184 /759;11 positive958 /117 or962 /115;15 positive80 /72 |
| `con-zfc-selective-2026-10-23.zip` | 19,615,180 /606 | 35,876,184 /640 | Separate native coefficient adapter B=2^429959,215,492 raw bytes; not bound into main equations |
| `con-zfc-sparse-pell-124c07c0b7.zip` | 15,502,748 /548;10,486,092 /603;10,127,484 /655 | 50,822,936 /582;34,378,296 /637;33,202,776 /689 | 11 positive954 /113, shifted system952 /108;12 positive897 /108, shifted system888 /102 |
| `con-zfc-support-majorants-2026-10-23.zip` | 29,157,244 /562;24,399,300 /568;20,754,916 /599;18,262,476 /624;15,534,796 /655 | 53,325,896 /595;39,914,856 /651 | Polynomial radical majorant changes; no variable-count record |
| `con_zfc_sparse_arithmetic_2026-10-23.zip` | 33,332,620 /682 | 54,768,104 /709 | 15 positive66 ops /degree157;68 /113;72 /80;74 /68 |
| `con_zfc_sparse_support_2026-10-23.zip` | 32,568,568 /652 | 59,564,744 /653 | 11 positive990 /117 or994 /115;15 positive44 /76 |

The quartic baselines remain 31 positive and 50 unrestricted integer
unknowns. All incoming low-variable constructions retain the same
31-positive,22-quadratic-residual parent. None claims a better quartic
variable count. The new quartic45 construction is therefore distinct from
these wave-7 results.

Previously explored mechanisms include support-sensitive isolation of 71
shifted or62 unshifted monomials against all528 possible pairs; shared
positive successor words; irregular target overlaps; sparse one-bit carry
padding; target population thresholds; interior block padding; smaller
radical majorants; seeded positivity guards; Y-denominator Pell quotient
absorption; midpoint carriers; squared auxiliary quotient congruences;
minimum-norm sum finalizers; and a complemented factorized receiver decoder.

## Formalization boundary

The active repository's `STATUS.md` and `OBJECT_ZFC.md` distinguish:

1. externally Lean-checked equivalences about the actual predicate
   `BProv ZFCax_s [] Form.fBot`;
2. ordinary mathematical proofs asserted formalizable in ZFC for explicit
   materialized compiler equations;
3. a literal object-language derivation of the final iff in ZFC's encoded
   syntax.

The third endpoint remains open. The active code has actual internal
addition totality/uniqueness proofs but has not assembled the two target
sentences and the requested final `BProv` derivation. None of the incoming
packages claims to close this endpoint. Its absence does not by itself
refute an ordinary proof that can be formalized in ZFC, but the two claims
must not be conflated.
