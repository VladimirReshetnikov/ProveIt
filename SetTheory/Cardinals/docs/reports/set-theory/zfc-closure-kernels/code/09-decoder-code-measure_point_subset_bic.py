#!/usr/bin/env python3
"""Regenerate source-02's exact PIBI/PISI template-size comparison.

Usage:
  python measure_point_subset_bic.py PATH/02-seeded-formulas.py [OUTPUT.json]

The source module is loaded unchanged. These are formula-tree metrics,
not program-node counts, machine-state counts, or a mathematical proof.
"""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def measure(source: Path) -> dict:
    source = source.resolve()
    spec = importlib.util.spec_from_file_location("source02_formulas", source)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load formula source: {source}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    templates = module.templates()
    measured = {}
    for name in ("Ext", "EC", "PIBI", "PISI_open", "SIBI"):
        constructors = module.count(module.expand(templates[name]))
        measured[name] = {
            "nodes": sum(constructors.values()),
            "constructors": constructors,
        }
    ext = measured["Ext"]["nodes"]
    old = measured["PIBI"]["nodes"]
    new = measured["PISI_open"]["nodes"]
    kinds = set(measured["PIBI"]["constructors"]) | set(
        measured["PISI_open"]["constructors"]
    )
    # The same theorem applies to the subset seed. Retain its entire
    # original conclusion and replace only its mixed-bound premise by
    # the subset-bound premise already present in PISI_open.
    subset_seed_subset_bound = module.Imp(
        templates["PISI_open"].args[0], templates["SIBI"].args[1]
    )
    subset_counts = module.count(module.expand(subset_seed_subset_bound))
    subset_nodes = sum(subset_counts.values())
    return {
        "source_file": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "status": "Exact syntax measurement; no machine-size or formal-proof claim.",
        "metric": (
            "Formula-tree nodes after source-02 expansion into membership, "
            "equality, bottom, implication, and universal quantification. "
            "Each schema-hole occurrence counts as one atom. Variable "
            "payloads and parameter closure are excluded."
        ),
        "source_templates": measured,
        "derived_templates": {
            "subset_seed_subset_bound": {
                "construction": "SIBI conclusion with PISI_open local-bound premise",
                "nodes": subset_nodes,
                "constructors": subset_counts,
            }
        },
        "comparison": {
            "schema_nodes_before": old,
            "schema_nodes_after": new,
            "theory_nodes_before_including_Ext": old + ext,
            "theory_nodes_after_including_Ext": new + ext,
            "nodes_saved": old - new,
            "schema_hole_occurrences_before": measured["PIBI"]["constructors"].get(
                "hole", 0
            ),
            "schema_hole_occurrences_after": measured["PISI_open"]["constructors"].get(
                "hole", 0
            ),
            "constructor_savings": {
                kind: measured["PIBI"]["constructors"].get(kind, 0)
                - measured["PISI_open"]["constructors"].get(kind, 0)
                for kind in sorted(kinds)
            },
        },
        "reflexive_seed_corollary": {
            "subset_seed_schema_before": measured["SIBI"]["nodes"],
            "subset_seed_schema_after": subset_nodes,
            "with_Ext_before": measured["SIBI"]["nodes"] + ext,
            "with_Ext_after": subset_nodes + ext,
            "equality_free_EC_control_before": measured["SIBI"]["nodes"]
            + measured["EC"]["nodes"],
            "equality_free_EC_control_after": subset_nodes + measured["EC"]["nodes"],
        },
    }


if __name__ == "__main__":
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    result = measure(Path(sys.argv[1]))
    encoded = json.dumps(result, indent=2) + "\n"
    if len(sys.argv) == 3:
        Path(sys.argv[2]).write_text(encoded)
    print(encoded, end="")
