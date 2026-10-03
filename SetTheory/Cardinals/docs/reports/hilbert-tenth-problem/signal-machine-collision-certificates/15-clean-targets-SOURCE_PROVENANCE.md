# Exact source provenance

Date: 3 October 2026

This is a separate extension. The frozen companion release 9 is unchanged. No public or collaborative document is created by this package.

The five vendor Python files are byte-for-byte copies of the frozen release dependencies. The cleanup exporter, checker, tests, mathematical theorem, and examples are byte-for-byte copies of the independently audited extension snapshot. The upstream extension manifest is retained as provenance; its optional audit note and console logs are not redistributed.

The standalone report is newly typeset from the proved extension and the stated compiler/lower-bound interface. It is not a modified copy of report 9. No universal source table is silently added.

## Portable audit adaptation

The independent audit algorithms are unchanged. Absolute dependency constants are replaced by paths relative to the package root; code/ references become vendor/; one certificate receipt uses source basenames instead of absolute keys, with its snapshot recheck adjusted consistently; the actual-CA console receipt label is made relative. All adapted harnesses are rerun by replay.py. Original and adapted script hashes follow. Original receipt keys containing source paths are normalized to matching relative names. The audit prose is adjusted only to explain this package layout.

audit/audit_lift_name_collisions.py
  Original SHA-256: 15ef132b58749e1acc366c89ca6306f9bde07ae537652f6310082e9d881a1948
  Portable SHA-256: 7ee6d1789d3cd50cf40037e16999fdf009dfada6656e13620843dc4db6ccae6f

audit/audit_actual_ca.py
  Original SHA-256: c04961e983262b45e609e49b506c77794823a028936799e1a2a63b03f3e94607
  Portable SHA-256: d2cd8aaf4c785eb72c0026e51124cb5c9cf574e60d3a56026040e534b7e1f244

audit/audit_certificates.py
  Original SHA-256: e50b3d9a6bd39a224ed1137730a380ade17b5989f9a330a884f377afddf19b45
  Portable SHA-256: b0959d1bbb5713add367ad557abb1872bfbef33ebf03ef16bc51dce0808a17f1

audit/audit_witness_lift.py
  Original SHA-256: 5bc294a7da4ff572809169f16fc9b36770f5f169b2d76ce30208d0d912eca12a
  Portable SHA-256: 178c5bc0869bdcc22edc5e03d00930ce080440c7ca6461ff765612d3c277b542

## Source hashes

The complete machine-readable ledger is provenance/source-provenance.json. The package SHA256SUMS covers the actual delivered files.

### extension source

clean_targets.py  a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315
check_clean_targets.py  51ce0665dcc74bc3cf2461a25344a8688b23258b9281205c68fabb0526881d72
test_clean_targets.py  d6a13ef03a9fb5b7deb64a74eca2f45051f6dc0bcab533b55d675f8af7e3d2eb
test_affine_lift.py  385b9015288bfc799ffd22868f786f9fb4edf3c221cd50d0ef5faf9b35e01c3e
CLEAN-TARGET-THEOREM.md  3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168

### frozen dependencies

radius_one.py  99cae9e9b3d1ceac7b34392e2fe32772daaa88394700ea0c820aa72d3fe5433c
spatial_radius_one.py  6842cecac0ce20e62d1b0ef18347e52d1db574e11c2d71c3f22a11abf6ae149b
checker.py  9fc3879eb24f4b4d9d2e1c8ebc0c123510c04141bd754547d191ceef28815c66
three_mass_collision_generator.py  14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52
certificate.py  fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8

### frozen companion

three-mass-report.tex  8bfdbf66399fa40bd4219497abb11c78cfece41b0a4270d9d742ad7111f7930b
three-mass-report.pdf  1fcaf9a57234e14a2d5d8dc6bc5ec33d50fd7ddc296dc36a67513e61533d4fba
SHA256SUMS  c9efd37d0c489d9ca3613a89846b2282b0b837558696bd161f7b85b55da0b581

## Reference verification

Morita and Imai (2001), Definitions 3.1–3.3, Proposition 3.4, and Lemma 3.5, were inspected in the primary paper. Bennett (1973) was inspected in a primary-paper copy; the report cites its DOI and that copy. The original three-agent geometric precedent is cited to Brandt, Portmann and Uitto (2020). No third-party PDF is bundled.
