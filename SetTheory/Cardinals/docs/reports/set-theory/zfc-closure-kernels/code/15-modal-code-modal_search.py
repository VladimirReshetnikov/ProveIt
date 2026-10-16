"""Finite coordinate-quantifier diagnostic for the published CP/GIC formulas.

Every quantifier changes its named coordinate to all domain points DISTINCT
from its present value. This is deliberately nonstandard first-order
semantics. Membership is irreflexive, so relative falsity Rel(0, 0) is false.
The exact CP/GIC syntax is loaded from pinned source, without copying it here.

Run from the archive root after machines/fetch_dependencies.py:
    python code/modal_search.py --output results/modal-search.json
An existing checkout can instead be supplied with --repo PATH.
"""
from __future__ import annotations

import argparse
import functools
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys
import time


if not __debug__:
    raise SystemExit(
        "Verification requires Python assertions; do not use -O, -OO, "
        "or PYTHONOPTIMIZE."
    )

ARCHIVE_ROOT = Path(__file__).resolve().parent.parent
PINS_PATH = ARCHIVE_ROOT / "machines" / "source_pins.json"
RESEARCH_PATH = Path("Computability/BusyBeaver/Research/ZFC")
REQUIRED_SOURCES = (
    str(RESEARCH_PATH / "theory_backend_experiment.py"),
    str(RESEARCH_PATH / "recover_wade_dag.py"),
    str(RESEARCH_PATH / "pairing_backend_experiment.py"),
    "lib/jeff-busy-beaver-zfc254/ZF/m254/tools/logic/spec.py",
)


def load_theory(repo: Path):
    """Check all imported research modules and the parsed spec before import."""
    pins = json.loads(PINS_PATH.read_text(encoding="utf-8"))
    verified = {}
    for relative in REQUIRED_SOURCES:
        expected = pins["files"][relative]
        actual = hashlib.sha256((repo / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source hash mismatch: {relative}")
        verified[relative] = actual

    # These three source files import only each other and standard-library
    # modules at initialization. Reject an already cached research module so
    # that the hashes above apply to the code actually imported in this run.
    module_names = (
        "recover_wade_dag", "pairing_backend_experiment",
        "theory_backend_experiment",
    )
    if any(name in sys.modules for name in module_names):
        raise RuntimeError("Run this diagnostic in a fresh Python process.")
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(repo / RESEARCH_PATH))
    theory = importlib.import_module("theory_backend_experiment")
    for name in module_names:
        actual_path = Path(sys.modules[name].__file__).resolve()
        expected_path = (repo / RESEARCH_PATH / f"{name}.py").resolve()
        if actual_path != expected_path:
            raise RuntimeError(f"Unexpected imported module origin: {name}")
    return theory, {
        "repository": pins["repository"],
        "commit": pins["commit"],
        "upstream_mira_jeff_snapshot_commit":
            pins["upstream_mira_jeff_snapshot_commit"],
        "verified_source_sha256": verified,
    }


def search(n: int, theory):
    spec, digest = theory.published_spec()
    container = spec["bundle_C"]("a", "b", "c")
    collection = spec["bundle_G"]("a", "b", "c")
    vals = list(itertools.product(range(n), repeat=3))
    assignments = {v: i for i, v in enumerate(vals)}
    allbits = (1 << len(vals)) - 1
    edges = [(a, b) for a in range(n) for b in range(n) if a != b]
    labels = {"a": 0, "b": 1, "c": 2}
    accessibles = {}
    for label, coord in labels.items():
        accessibles[label] = [
            [assignments[v[:coord] + (d,) + v[coord + 1:]]
             for d in range(n) if d != v[coord]]
            for v in vals
        ]

    def All(label, value):
        return sum(
            1 << i for i, row in enumerate(accessibles[label])
            if all(value >> j & 1 for j in row)
        )

    witnesses, cp_valid, first_failures = [], [], []
    gic_candidate_matrices_checked = 0
    direct_cp_checks = direct_gic_checks = 0
    start = time.perf_counter()
    for relation_mask in range(1 << len(edges)):
        relation = {
            edge for i, edge in enumerate(edges) if relation_mask >> i & 1
        }
        rel = {}
        for a in labels:
            for b in labels:
                rel[a, b] = sum(
                    1 << i for i, v in enumerate(vals)
                    if (v[labels[a]], v[labels[b]]) in relation
                )

        @functools.lru_cache(None)
        def evaluate(formula, phi):
            if formula == 1:
                return 0
            if formula == "c":
                return phi
            tag, a, b = formula
            if tag == "imp":
                return (allbits ^ evaluate(a, phi)) | evaluate(b, phi)
            if tag == "rel":
                return rel[a, b]
            if tag == "all":
                return All(a, evaluate(b, phi))
            raise ValueError(formula)

        def direct(formula, env, phi_mask):
            if formula == 1:
                return False
            if formula == "c":
                return bool(phi_mask >> (env[0] * n + env[1]) & 1)
            tag, a, b = formula
            if tag == "rel":
                return (env[labels[a]], env[labels[b]]) in relation
            if tag == "imp":
                return (not direct(a, env, phi_mask)
                        or direct(b, env, phi_mask))
            if tag == "all":
                coord = labels[a]
                return all(
                    direct(b, env[:coord] + (d,) + env[coord + 1:], phi_mask)
                    for d in range(n) if d != env[coord]
                )
            raise ValueError(formula)

        cp_truth = evaluate(container, 0)
        for i, env in enumerate(vals):
            assert bool(cp_truth >> i & 1) == direct(container, env, 0)
            direct_cp_checks += 1

        # For D=2, crosscheck GIC evaluators even when CP fails. Agreement of
        # evaluators does not assert that the evaluated formula is true.
        if n == 2:
            for phi_mask in range(1 << (n * n)):
                phi = sum(
                    1 << i for i, (a, b, c) in enumerate(vals)
                    if phi_mask >> (a * n + b) & 1
                )
                truth = evaluate(collection, phi)
                for i, env in enumerate(vals):
                    assert bool(truth >> i & 1) == direct(
                        collection, env, phi_mask
                    )
                    direct_gic_checks += 1

        if cp_truth != allbits:
            first_failures.append({
                "relation_mask": relation_mask,
                "axiom": "CP",
                "assignment": vals[next(
                    i for i in range(len(vals)) if not (cp_truth >> i & 1)
                )],
            })
            evaluate.cache_clear()
            continue

        cp_valid.append(relation_mask)
        checked = 0
        for phi_mask in range(1 << (n * n)):
            phi = sum(
                1 << i for i, (a, b, c) in enumerate(vals)
                if phi_mask >> (a * n + b) & 1
            )
            truth = evaluate(collection, phi)
            checked += 1
            gic_candidate_matrices_checked += 1
            if truth != allbits:
                first_failures.append({
                    "relation_mask": relation_mask,
                    "axiom": "GIC",
                    "phi_mask": phi_mask,
                    "assignment": vals[next(
                        i for i in range(len(vals)) if not (truth >> i & 1)
                    )],
                    "matrices_checked_through_failure": checked,
                })
                break
        else:
            witnesses.append({
                "relation_mask": relation_mask,
                "relation": sorted(relation),
                "matrix_count": 1 << (n * n),
                "assignment_count_per_matrix": n ** 3,
            })
        evaluate.cache_clear()

    return {
        "domain_size": n,
        "quantifier": "all distinct coordinate replacements",
        "relations_tested": 1 << len(edges),
        "assignments": len(vals),
        "relation_mask_edge_order": edges,
        "CP_valid_relations": cp_valid,
        "witnesses": witnesses,
        "first_failures": first_failures,
        "independent_direct_CP_crosschecks": direct_cp_checks,
        "independent_direct_GIC_crosschecks": direct_gic_checks,
        "independent_direct_boolean_crosschecks":
            direct_cp_checks + direct_gic_checks,
        "GIC_candidate_matrices_checked_after_CP":
            gic_candidate_matrices_checked,
        "elapsed_seconds": time.perf_counter() - start,
        "published_spec_sha256": digest,
        "scope": (
            "All IR relations on D are tested against exact named CP; only "
            "CP survivors are tested against exact named GIC for all binary "
            "matrices independent of fresh c. GIC evaluator crosschecks do "
            "not assert GIC validity. Nonstandard quantifier semantics."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo", type=Path,
        default=ARCHIVE_ROOT / "machines" / "upstream",
        help="Pinned ProveIt checkout (default: archive machines/upstream).",
    )
    parser.add_argument(
        "--output", type=Path,
        help="Write full results to this JSON path; otherwise print them.",
    )
    args = parser.parse_args()
    try:
        theory, provenance = load_theory(args.repo.resolve())
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        parser.error(str(exc))
    output = {
        "source_provenance": provenance,
        "sizes": [search(n, theory) for n in (2, 3)],
    }
    if args.output is None:
        print(json.dumps(output, indent=2))
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(output, indent=2) + "\n", encoding="utf-8"
        )
        print(json.dumps({
            str(d["domain_size"]): {
                k: v for k, v in d.items()
                if k not in ("first_failures", "relation_mask_edge_order")
            } for d in output["sizes"]
        }, indent=2))


if __name__ == "__main__":
    main()
