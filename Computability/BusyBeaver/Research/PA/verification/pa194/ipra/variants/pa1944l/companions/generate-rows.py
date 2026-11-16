"""Bind the retained timing/selector companions to the exact PA1944L literal."""

from pathlib import Path
from hashlib import sha256
import importlib.util
import json
import sys

repo, out = map(Path, sys.argv[1:])
sys.dont_write_bytecode = True
docs = repo / "Computability/BusyBeaver/Research/PA/docs"
variants = repo / "Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants"


def load_generator(name, source):
    spec = importlib.util.spec_from_file_location(name, source)
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    return generator


stem = "pa1944l_research_2026-11-14/machine/machine"
labels = "pa1944l_research_2026-11-14/machine/labels.json"
base_pin = "c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253"
labels_pin = "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b"
native_pin = "0867349f173d1a98287e5727114e0f210ed36e47f9e927cdf845b978c2ec72b5"
fast_pin = "481796e5f6b88cb73c35cf2c7cde543a1d9afa4b87c5b1e6f267ffd21cdc2f90"
selector_pin = "59b64faa9b5a0cd2facfc8676aeca9d2ecb87f50cdc8445a2c7b64d84072e5d3"
combined_pin = "2f02da57c72d820825a7b86e656d7c11ad86219ac0bdb3e46b5e4458e3962acc"
corpus = docs / "pa194_comparison_and_new_designs_2026-11-15/research/physical"
metadata = json.loads((corpus / "receipts/corpus_meta.json").read_bytes())
label_map = json.loads((docs / labels).read_bytes())
base = (docs / f"{stem}.tm").read_bytes()
assert sha256(base).hexdigest() == base_pin
assert sha256((docs / labels).read_bytes()).hexdigest() == labels_pin
readme = (docs / "pa1944l_research_2026-11-14/README.txt").read_text()
assert "native table uses initial label 74 and halt 254" in readme
assert (label_map[0], label_map[-1]) == (74, 254)


def literal_rows(raw):
    return [line.split() for line in raw.decode("ascii").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


rows = {(label_map[int(q)], int(b)): (int(w), direction, label_map[int(t)])
        for q, b, w, direction, t in literal_rows(base)}
native = "".join(f"{q} {b} {w} {d} {t}\n"
                 for (q, b), (w, d, t) in sorted(rows.items())).encode("ascii")
assert sha256(native).hexdigest() == native_pin
overlays = {fast_pin: ["f"], selector_pin: ["sel"], combined_pin: ["f", "sel"]}
for digest, patches in overlays.items():
    raw = (corpus / "inputs/corpus" / f"{digest}.tm").read_bytes()
    assert sha256(raw).hexdigest() == digest and len(literal_rows(raw)) == 388
    assert all(line[0:1].isdigit() for line in raw.splitlines())
    assert metadata[digest] == {"base": native_pin, "patches": patches}

out.mkdir(parents=True, exist_ok=True)
# Supply the sidecar under the naming convention used by the shared timing generator.
mirror = out / "packet"
timing_path = mirror / stem
timing_path.parent.mkdir(parents=True, exist_ok=True)
for link, target in (
    (timing_path.with_suffix(".tm"), docs / f"{stem}.tm"),
    (timing_path.with_suffix(".labels.json"), docs / labels),
    (mirror / corpus.relative_to(docs).parts[0], docs / corpus.relative_to(docs).parts[0]),
):
    if link.is_symlink():
        assert link.resolve() == target.resolve()
    else:
        link.symlink_to(target.resolve())
fast = load_generator("timing_rows", variants / "pa194fast/generate-rows.py")
fast.REFERENCE_MODULES["4L"] = "PA1944LData"
fast.generate(mirror, out, "4L", (stem, base_pin, labels_pin, fast_pin))
selector = load_generator("selector_rows", variants / "pa194sel/companions/generate-rows.py")
selector.PARENTS["4L"] = (f"{stem}.tm", labels, base_pin, labels_pin, fast_pin,
                         selector_pin, combined_pin, "PA1944LData", "rows")
for timing in (False, True):
    selector.generate(repo, out, "4L", timing)
