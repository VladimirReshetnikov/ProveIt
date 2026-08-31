# Representation-source snapshots

This file separates historical source identity from live canonical integrity.
Arrival ledgers are historical evidence and are not rewritten.

## Git snapshots

- Complete pre-retirement tree containing all ten absorbed report directories:
  443793e846934e7363e314ea01129b9f50197a58
- Base Lagrange report and v5 audit: 4544e9af6b94820402c69967be1dff3f85e43c1e
- Lagrange v6 corpus audit: 57c2ad230e11dfd4dc3aa9aabd2a35db51331415
- Base Legendre spectral-closure report:
  73c85cb0023615311fdc4a5ff4951767bddeff34
- Legendre self-reconstruction report:
  faa3a9b94ac0e71abdc53c36fdf428222e4d2a8c
- Earlier exact-polynomial report:
  5915d9a723c9ae01a2cc4be8a251bdcb11d9e406
- Consolidation merge baseline:
  9c952b242600e58c257c0975d38a658e50264681
- Baseline parents:
  c9b734ad92295309fbf0393cb6fdac4b3a7e23e7 and
  eb4a8613c4644e2e7e862c4180139af82cdc203e

## Main-source SHA-256 values

- rvachev_lagrange_loop_report:
  5d17373e36f6b12576a9add8c46fde57ae2e59b2b93410930fe64fb39f6dd647
- Lagrange_Rvachev_Loop_Package:
  978aeadec8087c5c44881ccc22b87fa2c3c5579aa539a462621c5418d066e4fb
- lagrange_rvachev_loop_report_v3:
  07587a69794e72f18af9075eae545f0cd5ae1694f318b961d287713a088a1465
- Lagrange_Rvachev_Closed_Loop_Report:
  727ccd7491844ffc4f2d0a82f351e052e83f50acbfcb76f7d12aad0059f95099
- Rvachev_Lagrange_Loop_Report_v5:
  118a09539feafbccf24e353e6e6c0c2e647236fb77822eadba721adc4c38808d
- Rvachev_Lagrange_Loop_Report_v6:
  e11a2c460ae2b5f33b80217a681dfae874398b8f22c8edcd8d351b5eaeeac0b2
- legendre_rvachev_closed_loop:
  bebd04fe47a308328d717028876e78f93c89d6d33238e54690c16d32bfb6a2db
- Legendre_Rvachev_Closed_Loop_Report_v3:
  8bbd922a51dbc6a132892c43c226d57fda220f0b41550c2d27cd90f97ed324d2
- Legendre_Rvachev_Closed_Loop_Report_v4:
  7eff3989000e82f72f4b9e9761f75b807ec95bf369f46b67d96abce207594274
- Legendre_Rvachev_Self_Reconstruction:
  23180ac9e6ed8bfc9c9d0e7e01d97890b2414768fef982d7a1563083fdba8376

## Exact root-geometry evidence

The two authoritative v3 data artifacts are retained byte-for-byte at their
canonical paths; their arrival and canonical SHA-256 values therefore agree:

- Q12 certificate, arrival and canonical:
  550ed1645e372f4a2e7c54f9bd05afb331e673ae73ff51f73f378925070a3b4f
- root-count table, arrival and canonical:
  7626ea0429e0c748d895d7d8df2c4825175aa04cd8b9cf7d83bace7a7546b69a
- canonical verifier:
  25481f2d2fd1a9a07f32c56e535c0814a7b504947bfd23bf0f1b7548a659fc0d

The focused replay command is:

    python -B assets/evidence/legendre/root-geometry/verify_sturm.py

Its expected exact result is: all Sturm counts for
$Q_1^-,\ldots,Q_{20}^-$ verify, and $Q_{12}^-$ has eight real roots.

The v6 source arrived without the companion corpus index, CSV, extractor, or
plots described by its prose. That missing-at-arrival boundary is part of the
provenance and must not be silently repaired by invented artifacts.
