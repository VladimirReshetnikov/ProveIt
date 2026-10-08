"""Reproduce full native normal-topology queries and their certificate costs.

The layered-solid-torus family and explicit polygon oracle are inherited
from the preceding affine-families report. The native Regina control is an
independent C++ implementation, not the baseline Python orbit algorithm.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "normal_orbit_research"))
from fixtures import layered_torus, regina_components, regina_triangulation
from reference_geometry import expanded_components
from fastunknot.normal_components import analyze_normal_surface, verify_normal_surface_certificate
from fastunknot.normal_interval_extraction import encode_large_integers, extract_normal_intervals


def snapshot():
    paths = [ROOT / "fastunknot" / name for name in (
        "interval_orbits.py", "interval_orbit_verify.py", "normal_components.py",
        "normal_interval_extraction.py", "integer_codec.py")]
    paths += [ROOT / "normal_orbit_research" / name for name in ("fixtures.py", "reference_geometry.py")]
    paths.append(Path(__file__))
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest() for path in paths}


def component_summary(components):
    return {"components": len(components),
            "orientable_components": sum(c["orientable"] for c in components),
            "nonorientable_components": sum(not c["orientable"] for c in components),
            "boundary_components": sum(c["boundaries"] for c in components),
            "closed_components": sum(c["boundaries"] == 0 for c in components),
            "euler_characteristic": sum(c["euler"] for c in components),
            "normal_discs": sum(c["discs"] for c in components)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "results/normal_orbits_20261008.json")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--sizes", type=int, nargs="+", default=[1, 4, 8, 12, 16, 32, 64, 128])
    args = parser.parse_args()
    if args.rounds < 1 or any(n < 1 for n in args.sizes):
        parser.error("rounds and sizes must be positive")
    rng = random.Random(2026100812)
    source = snapshot()
    try:
        import regina
        regina_version = regina.versionString()
    except ImportError:
        regina_version = None
    rows = []
    for n in args.sizes:
        raw, coordinates = layered_torus(n)
        proof_result = analyze_normal_surface(raw, coordinates, record_trace=True)
        expected = proof_result["summary"]
        certificate = proof_result["certificate"]
        assert expected["certifies_compressing_disk"]
        assert verify_normal_surface_certificate(raw, coordinates, certificate)
        operations = {
            "native_count": lambda: analyze_normal_surface(raw, coordinates),
            "native_proof": lambda: analyze_normal_surface(raw, coordinates, record_trace=True),
            "native_replay": lambda: verify_normal_surface_certificate(raw, coordinates, certificate),
        }
        if expected["normal_discs"] <= 20000:
            operations["literal_polygon"] = lambda: component_summary(
                expanded_components(extract_normal_intervals(raw, coordinates)))
        # Regina's components() explicitly builds normal discs (as its public
        # API documentation warns); keep this oracle on the same finite cap.
        if regina_version and expected["normal_discs"] <= 20000:
            operations["regina_components"] = lambda: component_summary(
                regina_components(regina_triangulation(raw), coordinates))
        samples = {name: [] for name in operations}
        for repeat in range(args.rounds):
            order = list(operations)
            rng.shuffle(order)
            for name in order:
                started = perf_counter()
                output = operations[name]()
                elapsed = perf_counter() - started
                samples[name].append(elapsed)
                if name == "native_replay":
                    assert output is True
                elif name.startswith("native_"):
                    assert output["summary"] == expected
                else:
                    assert all(expected[k] == v for k, v in output.items()), (name, n, output, expected)
        encoded_certificate = json.dumps(encode_large_integers(certificate), separators=(",", ":"))
        rows.append({"tetrahedra": n, "input": {"triangulation": raw, "coordinates": coordinates},
                     "summary": expected, "extraction": proof_result["extraction"],
                     "orbit_stats": proof_result["orbit_stats"],
                     "proof_json_bytes": len(encoded_certificate.encode()),
                     "raw_seconds": samples,
                     "median_seconds": {k: median(v) for k, v in samples.items()},
                     "literal_status": "completed" if "literal_polygon" in samples else
                                       "not run: exceeds fixed 20,000-disc oracle allowance",
                     "regina_status": "completed" if "regina_components" in samples else
                                       "not run: unavailable or exceeds fixed explicit-disc allowance"})
        print(json.dumps({"tetrahedra": n, "disc_bits": expected["normal_discs"].bit_length(),
                          "medians": rows[-1]["median_seconds"]}), flush=True)
    assert source == snapshot(), "measured dependency changed during timing"
    result = {"python": sys.version, "platform": platform.platform(), "regina": regina_version,
              "rounds": args.rounds, "seed": 2026100812,
              "source_sha256": source, "source_hashes_unchanged": True,
              "scope": "supplied normal vectors, full native aggregate topology, proof and replay; "
                       "no normal surface search or whole knot recognition timing",
              "warmup": "one native proof generation and one replay per input before shuffled timing",
              "controls": "literal polygons and Regina compute listed topology subset, also individual "
                          "component vectors; neither is a full identical certificate protocol",
              "rows": rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(encode_large_integers(result), indent=2) + "\n")
    example_dir = ROOT / "normal_orbit_research/examples"
    example_dir.mkdir(parents=True, exist_ok=True)
    raw, coords = layered_torus(1)
    (example_dir / "meridian.json").write_text(json.dumps({"triangulation": raw, "coordinates": coords}, indent=2) + "\n")
    raw, coords = layered_torus(32)
    proof = analyze_normal_surface(raw, coords, record_trace=True)
    (example_dir / "fibonacci32_certificate.json").write_text(json.dumps(
        encode_large_integers({"triangulation": raw, "coordinates": coords,
                               "certificate": proof["certificate"]}), separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
