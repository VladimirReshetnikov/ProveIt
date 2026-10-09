# Optional normal-surface portfolio

The numeric PD fixtures were generated with Regina 7.4.1:

```python
import json
import regina
from pathlib import Path

for name in ('monster', 'gordian', 'gst'):
    link = getattr(regina.ExampleLink, name)()
    Path(name + '.json').write_text(json.dumps({'pd': link.pdData()}))
```

The [official ExampleLink documentation](https://regina-normal.github.io/engine-docs/classregina_1_1ExampleLink.html)
identifies Monster as a ten-crossing unknot and Gordian as Haken's
141-crossing unknot. GST is the 48-crossing Gompf–Scharlemann–Thompson knot
from *Fibered knots and potential counterexamples to the property 2R and
slice-ribbon conjectures* (2010), Figure 2. It is not an unknot fixture.

From the `fast` directory, install the optional package extra and run:

```sh
python -m pip install '.[normal]'
python -B normal_research/benchmark.py --output results/normal_surface_local.json
```

The checked-in run uses Python 3.13 and Regina distribution 7.4.1. It compares
fresh-PD validation plus complete recognition with a four-second global limit
and 50,000-object Khovanov ceiling. Five shuffled paired rounds follow one
excluded warm-up. The default and identical control are compared with
`use_regina=True`, using a two-second native allowance. Each native call starts
a fresh child interpreter; startup and cleanup count toward query time.

Gordian finishes in all five portfolio runs (median 1.788 seconds), while both
default arms finish none under the four-second allowance. Do not treat the
default's censored durations as completed recognition times. The other three
inputs remain on the existing fast paths and all conclusive results agree.
Separate standalone queries show why unconditional native dispatch would be
poor: Monster takes 0.278 seconds and GST exceeds three seconds, while their
built-in recognition takes about one and two milliseconds respectively.

The native worker resets Regina's random engine to its default seed. This
makes the measured simplification sequence reproducible on this build and
platform, not across all library versions and machines. Evidence explicitly
trusts the external exact engine; this wrapper does not export a native
normal-surface proof. The separate `--normal-seed` stage now constructs
source-bound cocycle candidates and independently checks positive disc
certificates; see the main implementation README. The article describes
both trust boundaries. No general subexponential bound is claimed.
