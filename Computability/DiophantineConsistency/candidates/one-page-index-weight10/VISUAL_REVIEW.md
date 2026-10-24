# Root visual and rendering review

The complete PDF was rasterized with pdftoppm at a 1600-pixel long edge
and inspected. It is one Letter page with a 9-point main body. The title,
ten unknowns, every arithmetic line, boxed equation, four constant recipes,
tile table, decoder, ordered alphabet, all seed lines and footer fit
without clipping or collisions. The PDF has no overfull TeX boxes.

Both normal and optimized renderings have identical PDF, TeX, polynomial
and seed hashes. Extracted text retains all 436 seed characters, the full
62-character alphabet and all sixteen checked Greek/ell glyphs. Both full
tuple reconstructions reproduce all four payloads, 430 transitions, 943
tiles and 66,062 native basis/convolution identities. Their combined raw
coefficient size remains 295,388 bytes. Constants are complete on the page.

PDF SHA256: `a41fdda9c4129f8607b43805ffd2ce0b57d5d3013da7e58c3f4f578322ab8ea1`.
TeX SHA256: `0b540714a5b572dfa319117c90ad5417a63afe5566cf07649c11f500d9db81f9`.

The preview is a visual check; the separate symbolic front proof, actual-TeX
parser and ordinary source proof establish the arithmetic claims. No Lean
run, internal-ZFC theorem or actual absence of zeros is asserted.

The retained TeX diagnostic text strips trailing whitespace and final empty
lines; the rendering stdout and all mathematical artifacts are preserved.
