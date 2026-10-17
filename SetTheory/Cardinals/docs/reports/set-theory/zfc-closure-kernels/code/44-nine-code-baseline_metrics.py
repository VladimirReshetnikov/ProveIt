#!/usr/bin/env python3
"""Reconstruct the initial, unshared twelve-function comparison kernel."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import ground_kernel as K


def generate(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    native = K.source_clauses()
    fs = K.signature() + [("F", 2), ("S", 3)]
    native[9][1] = K.R("b", "t", K.f("F", "b", "t"), K.f("Y", "b", "t", "u"))
    native[14][2] = K.R("b", "t", K.f("S", "b", "t", "y"), "y")
    complete = native + K.equality_clauses(functions=fs)
    result = {
        "variant": "initial unshared F/H and Y/S witnesses, separate D",
        "functions": fs,
        "native": K.metrics(native, functions=fs),
        "equality_free": K.metrics(complete, functions=fs),
    }
    assert result["equality_free"]["clauses"] == 32
    assert result["equality_free"]["literals"] == 91
    assert result["equality_free"]["term_nodes"] == 339
    assert result["equality_free"]["template_bits"] == 2067
    for suffix, value in [("native", native), ("complete", complete), ("metrics", result)]:
        (output / ("unshared_initial_" + suffix + ".json")).write_text(
            json.dumps(value, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    print(json.dumps(generate(parser.parse_args().output), indent=2))
