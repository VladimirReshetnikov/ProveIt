# Explicit inherited calibration source

This directory preserves, byte for byte, the mathematical proof fragments,
two calibrated table files, claims and provenance from the **updated incoming**
AX11H packet at ProveIt commit
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

The source archive is `docs/incoming/pa194_ax11h_research_2026-11-14.zip`,
SHA-256 `93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.
`INHERITED_MANIFEST.json` binds the copied files and the exact source archive.
`SOURCE_README.md` is the original author's description and proof claim.
The original notice and licenses remain unchanged.

These files are an explicitly inherited mathematical dependency of the new
construction, not new work in the current package. The manuscript claims a
complete ordinary written iPRA equivalence for PA194AX11H and PA194QAX11H.
The new report states its own relative preservation theorem and explains the
composition with this cited absolute theorem. No new end-to-end Lean or Rocq
kernel check of the inherited calibration is claimed.

Most `.tex` files are fragments intended for the original report's preamble;
they are preserved for inspection and attribution, not advertised as ten
independently compilable documents. `physical_ipra_audit.tex` is standalone.
The fragments cite pinned upstream source constructors. This small excerpt
does not duplicate the entire upstream Lean development or the source
packet's independent executable verifiers. The main new archive's report and
proof-status note distinguish finite replay from uniform arithmetic proof.
