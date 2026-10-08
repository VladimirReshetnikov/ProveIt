# Source audit and provenance

Read date: 2026-10-08. Repository snapshot:
`04d799b69d388f75ce85539b26fca1585f9d2651`.

- `Topology/UnknotRecognition/fast/fastunknot/group_certificate.py`
  Git blob: `922510eda5b7e6731de43e639c7dafcb47a56361`.
  Audited presentation construction, integer min-cut search, singleton
  elimination, and independent elementary certificate replay.
- `Topology/UnknotRecognition/fast/fastunknot/diagram.py`
  Git blob: `8717f530cc2847492858da46ac4ac40a2288b7ee`.
  Audited checked PD and braid entry points, the odd-slot overpass convention,
  one-component and spherical-rotation-system requirements, and the bare
  constructor's validation boundary.
- `Topology/UnknotRecognition/fast/normal_research/gordian.json`
  Git blob: `2e1e9862299030c102a903818121f712b3ad10f8`.
  The shipped numerical PD is reformatted, not a byte-identical Git blob.
  Its 141 crossings, 143 faces, and single component were checked locally.
- `Topology/UnknotRecognition/fast/README.md`
  Git blob: `7d2d621f2440020dd4c678e5ac53b0dbce73fc86`.
  Used to identify maintained interfaces and distinguish integrated work
  from proposed or incoming research.

Individual files were read through the GitHub connector. A complete checkout
was not obtained. No upstream suite was run and no repository write was made.
The package's 49 passing tests are local tests, not the maintained suite count.

Theoretical context was checked against primary sources: Roig--Ventura--Weil
on Whitehead minimization, Papakyriakopoulos's free-cyclic knot-group theorem,
Kapovich's 2026 compressed primitivity preprint, and Lackenby's 2026 hierarchy
preprint (especially Section 9). Full bibliographic details and links are in
the article. No third-party PDFs or font files are redistributed.
