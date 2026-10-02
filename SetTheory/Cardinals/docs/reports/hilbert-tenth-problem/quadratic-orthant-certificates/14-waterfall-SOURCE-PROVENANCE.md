# Source provenance

## Fixed machine data

Creator: Iijil (GitHub account Iijil1), MTGPrograms repository. These are prior-art machine specifications, not a new universal machine discovered by this note.

- Included file: `source/UniversalTM15x2.twm.txt`
  - Source: https://github.com/Iijil1/MTGPrograms/blob/main/Examples/UniversalTM15x2.twm.txt
  - SHA-256: `52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a`
  - Bytes: 5414
- Included file: `source/UniversalTM15x2.tm.txt`
  - Source: https://github.com/Iijil1/MTGPrograms/blob/main/Examples/UniversalTM15x2.tm.txt
  - SHA-256: `ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae`
  - Bytes: 227

The matrix is a 47-by-47 serialization containing 46 actual clocks. Source rows are trigger vectors; the article's destination-row/source-column matrix is their transpose. The exact two source files were preserved byte for byte. Their hashes are the immutable identity used in this package; the cited repository branch may change later. Sources were inspected for this task on 2 October 2026.

The upstream compiler, credited but not copied into this package:
https://github.com/Iijil1/MTGPrograms/tree/main/TMtoTWM

## Primary universal-machine source

Turlough Neary and Damien Woods, Four Small Universal Turing Machines, Fundamenta Informaticae 91(1) (2009), 123–144.

- Published DOI: https://doi.org/10.3233/FI-2009-0036
- Publisher metadata: https://journals.sagepub.com/doi/10.3233/FI-2009-0036
- Author-hosted primary PDF: https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf
- Author-deposited archive: https://mural.maynoothuniversity.ie/id/eprint/12416/

The deposited PDF has incorrect printed pagination, as the archive explicitly notes. Its header also carries a different DOI. The bibliography uses publisher/archive metadata, not those erroneous header fields. Table 16 is on PDF page 17 (one-based); the input and halting configurations are inspected in the primary paper. On PDF page 19, the displayed halting configuration agrees with Table 16's undefined (u10,b) instruction, while nearby prose says c. The matrix and article use the table and displayed configuration. State u15 reading b moves right to u14.

No primary-paper PDF or image is included in this package.

## Waterfall semantics

Esolang specification, fixed revision 193038:
https://esolangs.org/w/index.php?title=The_Waterfall_Model&oldid=193038

The note uses the standard integer version: all clocks initially positive; all trigger increments nonnegative; positive nonhalt self-resets; all-zero halt trigger; simultaneous minima undefined. It does not silently substitute Flooding Waterfall semantics or a tie-breaking rule.
