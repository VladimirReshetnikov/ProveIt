# PA194 site-27 six-register scan and rewind

`PA194SixRewind.sixTo17` proves the physical rewind of six traversed blocks
from state 14 to state 17, with exact model-valued clock and a named remaining
tail. `PA194Site27ScanRewind.scanAndRewind` composes the suffix-preserving
six-block scan from state 71 with that rewind. It reconstructs the six
physical registers on the right tape and retains the selected-register
payload and arbitrary following suffix.

`PA194Site27To17.site27To17` composes the result from the original site-27
header. All logical registers, the header length, and the numeric suffix are
arbitrary model elements; its clock and both resulting tape halves are
explicit. The result is an intermediate state-17 configuration. It is not
yet a complete site-27 source step or the existing marker theorem's stronger
precondition.

`check-site27-to17.sh` recompiles the earlier ten site-27 modules and these
three additional modules against the five previously checked input overlays
described in `TWO-HEADER-PASSES.md`. The supplied overlays need an independent
audit of their coherent transitive import closure. Direct object hash checks
alone do not establish it. `PA194_TWO_PASSES_SOURCE_DIR` may point to external
sources. The theorem is model-uniform semantic execution; this module does
not itself construct an iPRA derivation.
