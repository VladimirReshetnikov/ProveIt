# Report64 visual revision and author verification

Final candidate d is 21 pages. PDF SHA-256: c86cb407ffb93a37625d0d0a25e86bf2d0434eaee1104e3059a3b002d0210608. Standalone LaTeX SHA-256: 52618709e5354630dacf5c33f18595605f6a8dd4e6d5ea1f6f44bc4bbc8a886e.

The author inspected all 21 preliminary page montages, then full-size final title/theorem, diagram, certificate table and appendix pages. The independent manuscript reviewer and final coordinator separately perform direct all-page inspection; their own acceptance records bind the final bytes.

Candidate b was not delivered. Its figure trajectories were correct, but four annotation nodes lacked TikZ's `at` keyword and appeared at the origin. The final source adds the keyword and places both event captions away from trajectories. The diagram's rational path coordinates do not change. The certificate table gains explicit count/degree column padding. The appendix is condensed to a clean full page, keeping all scientific/execution boundaries and referring exact integrity pins to the README. It no longer spills seven lines onto an otherwise blank final page.

`qa/visual-revision/b-to-d.patch` records all source edits. The before image is explicitly historical QA evidence, not the final figure. Final changed-page images are included separately. At the same 120 dpi, final d pages 1-2, 4-8, 10-17 and 19 are byte-identical to b. Changed pages are 3 (contents), 9 (figure annotations), 18 (table padding), 20 (appendix starts on the following page), and 21 (compact full appendix). Page 22 was removed. Final d has no overfull box or unresolved reference/citation warning.

The locked final build passed with every PNG CRC and raster validated and exact packaged PDF equality. Its final promoted receipt is the authoritative successful equality result; earlier build receipts predate promotion of their respective PDF candidate.
