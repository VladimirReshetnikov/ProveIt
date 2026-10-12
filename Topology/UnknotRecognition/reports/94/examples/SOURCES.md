# Example source parameters

`prism_100bit.json` is the arithmetic certificate generated from the modular path
with `N = 2**100 + 1`, `step = 2`, `start = 0`, multiplied by the four-triangle
fan returned by `disk_fan(4)`. Reproduce it with:

```sh
python code/demo.py --bits 100 --output rebuilt_prism.json
```

`path_9.json` uses `N = 9`, `step = 2`, `start = 0`. Its vertex ranks in source
numerical order are `16, 6, 14, 4, 12, 2, 10, 0, 8`. The edge rank is its tail's
vertex rank minus one. This is the analytic example in the article; the general
offset solver may add a harmless common constant instead.

These files serialize arithmetic packets, not independent native source geometry
certificates. `code/verify.py` therefore reports no ball or knot verdict. The
source-specific product demonstration establishes its own source through the
explicit constructor, the disk check and the product theorem. Replacing its
packet by unrelated source data requires a new source-binding proof.
