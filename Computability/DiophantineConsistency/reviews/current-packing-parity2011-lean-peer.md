# Current packing parity: independent Lean review

PASS. Reviewer: `complemented47_review`; author: root. I read all76 main
lines, all32 check lines, the complete imported packing-rank module, the
actual packing Facts, and the relevant mask and repunit definitions before
fresh replay. No source correction is requested.

I did not author this packet, the packing-rank proof, or the literal masks.
I authored older cyclic carry/word and tile calibration/permutation
dependencies, and the separate controller and rank-stride packets. This
review is independent of the new parity argument, not of every transitive
prerequisite.

| Frozen source | SHA-256 |
|---|---|
| `CurrentPackingParity2011.lean` | `78ac7146d33518ee410891d93df7d19384adc2fca5b2970f2a1a090841de99bb` |
| `CurrentPackingParity2011Checks.lean` | `782af23ed0970db09398bc193ac51d13ba3c9f4d8f2119f07e5d8b42d648eb64` |
| `CurrentPackingRank2011.lean` | `614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546` |
| `CurrentMasks2011.lean` | `72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06` |
| `NativeMaskPopulation.lean` | `a98b8175934f6c766933bfdc44d380b349f5b4ba27cf4a46582b0a0352431fc7` |

All source paths are under `Lean/DiophantineConsistency/`, relative to
`Computability/DiophantineConsistency/`.

The proof uses the actual adjusted low mask `M = lowPort*J+1`. The literal
low port is2 modulo4, while the repunit is1 modulo4, so M is3 modulo4.
Reducing the actual acceptance equation `(C-1) &&& M = 0` modulo4 therefore
forces `(C-1)%4=0`. This retains the origin adjustment; mere evenness of
the unadjusted low port would be insufficient. The focused negative check
records that distinction.

The actual q is divisible by4. Thus all positive-q blocks of `fourBlocks`
vanish modulo4, leaving precisely the preceding source digit and adjusted
mask; their sum is3. The generic modular helper avoids reducing the huge
closed port values and does not change the statement being proved. Natural
subtraction in this arithmetic lemma is harmless even for C=0. The later
conversion to the integer rank separately derives C>0 and C+F<q from the
same supplied packing Facts, so it does not silently identify truncated
subtractions with signed ones.

The final `packing_rank` uses the existing population witness and proves
that this very R equals the four-block natural expression. Its integer
binding, population `sigma 2 R = 3*(width*N)+2`, residue R%4=3, expression
R=2*r+1, and strict growth all refer to the same source, normalized digits,
dummy controls, stride, and carry Facts. It neither chooses another rank
nor assumes an auxiliary Pell solution, a source-system zero, or a desired
rank residue. It still requires the explicit coherent packing Facts;
constructing the final rank-calibrated packing and equation converse is
separate work.

I freshly compiled main and checks sequentially with `lean -M6000 -j1`,
each using `Elab.async false`. The isolated object namespace was
`/tmp/current-packing-parity2011-complement-peer-pc7moiau/lib/DiophantineConsistency`.
Unchanged prerequisites were symlinked into that namespace, excluding both
reviewed object bundles. `LEAN_PATH` was prepended after `lake env`, so
the checks imported the freshly compiled main. This was a fresh two-module
replay, not a rebuild of the full prerequisite closure.

Both first replay attempts exited zero: main3.49seconds, peak RSS
3,357,504KiB; checks2.87seconds, peak RSS3,333,176KiB. The main log is empty;
checks have no warnings or errors. All four axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Both produced objects are
byte-identical to the author's shared objects. The reviewed sources contain
no new axiom, `sorry`, or `native_decide`.

| Replay artifact | SHA-256 |
|---|---|
| Main object | `f6564153ebfd19713c40190c0cbb453ddf357663780f01e0ab9623e2b467336a` |
| Checks object | `bf9e1640e5ed97e18f08a090b7275622440affa871e78612d53051a438678928` |
| Main log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Checks log | `d70cef7c549006c16d77524f167bfa0b568fa58008e4210827fadb0b57b3160b` |
| Before and after input manifests | `b43d59b5cbe708a31be6aae8ba541c751f2d145cc0456f347f9b25f58c042445` |
| `REPLAY.json` | `0ebde605ec574e7f96b781cc04e76e6709658df91c42c048d8dc688bdd04b1b9` |

All12 pinned source/object inputs remained unchanged. Only this peer receipt
and temporary replay artifacts were written; no frozen source, shared
object, central document, or Git state was modified.
