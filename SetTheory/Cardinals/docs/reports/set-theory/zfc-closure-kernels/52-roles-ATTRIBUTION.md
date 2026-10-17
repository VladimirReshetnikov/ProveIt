# Attribution and licensing

This research packet was prepared for Vladimir Reshetnikov for incorporation into ProveIt. The newly written report, research scripts and independent audit notes are supplied under the MIT No Attribution (MIT-0) terms in `LICENSE`.

Retained source material comes from the ProveIt revision recorded in `provenance.json`. The existing 252-state construction, compiler experiments, numerical coding, phase analysis, symbolic register-box checker and proof interfaces are prior work. They are not claimed as newly constructed here.

The machine ancestry includes Mira-Cult's register program and literal machine, Jeff Ketchersid's verification, Andrew J. Wade's compiler framework, mira-emmy's public 253-state reduction, Vladimir Reshetnikov and other ProveIt contributors, and the attributed source-27 symbolic checker. The ProveIt materialization retains its original source comments and license. The vendored upstream snapshot is `jeff87654/busy-beaver` commit `297ab8df7e5de329605c3875b4934643b371a5e3`; the public PR-20 reduction is identified by the upstream notes and baseline audit.

Retained license and provenance files include:

- `vendor/ProveIt/LICENSE`
- `vendor/ProveIt/lib/jeff-busy-beaver-zfc254/README.proveit.md`
- `vendor/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/generator/LICENSE.wade`
- `research/machine_reduction/input-provenance.json`

The finite induced-HF graph representation and register coalescing ideas are not claimed as historically new mathematics or compiler theory. The contribution here is their application, implementation, exact certificates and measured limits in the specified state-reduction problem.
