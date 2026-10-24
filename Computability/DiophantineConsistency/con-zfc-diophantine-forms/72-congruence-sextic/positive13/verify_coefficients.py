#!/usr/bin/env python3
"""Authenticate and regenerate the four fixed positive13 coefficients offline."""
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    binding = json.loads((HERE / "ACTIVE_BINDING.json").read_text())
    packet = HERE / binding["polynomial_path"]
    need(hashlib.sha256(packet.read_bytes()).hexdigest() ==
         binding["polynomial_sha256"], "Literal polynomial binding mismatch")
    values = {}
    payloads = {}
    for name, record in binding["ports"].items():
        compressed = (HERE / record["path"]).read_bytes()
        raw = gzip.decompress(compressed)
        need(hashlib.sha256(compressed).hexdigest() ==
             record["sha256_gzip"], "Compressed coefficient hash: " + name)
        need(hashlib.sha256(raw).hexdigest() ==
             record["sha256_raw"], "Raw coefficient hash: " + name)
        need(len(raw) == record["raw_bytes"], "Coefficient byte count: " + name)
        value = int.from_bytes(raw, "little")
        need(value.bit_length() == record["bits"], "Coefficient bit count: " + name)
        need(raw == value.to_bytes((value.bit_length() + 7) // 8, "little"),
             "Noncanonical coefficient bytes: " + name)
        values[name] = value
        payloads[name] = raw
    beta = values["beta"]
    need(beta == (1 << 590069) - 1, "Wrong radix")
    need(beta % 3 == 1 and (beta + 1) % 3 == 2, "Fixed congruence facts")
    need(0 < values["MC"] < beta, "Low mask bounds")
    need(beta < values["MF"] < 2 * beta, "Shifted high mask bounds")
    need(values["K0"] > 0, "Positive transport constant")
    recipe = HERE / "native"
    with tempfile.TemporaryDirectory(prefix="positive13_coefficients_") as dirname:
        temporary = Path(dirname)
        for name in ["build_coefficients.py", "k215_transitions.json"]:
            shutil.copyfile(recipe / name, temporary / name)
        args = [sys.executable]
        if sys.flags.optimize:
            args.append("-O")
        args.append(str(temporary / "build_coefficients.py"))
        result = subprocess.run(args, text=True, capture_output=True, check=True)
        generated = json.loads(result.stdout)
        for name, basename in [("beta", "beta"), ("K0", "K"),
                               ("MC", "MC"), ("MF", "MF_source")]:
            raw = gzip.decompress(
                (temporary / "coefficients" / (basename + ".bin.gz")).read_bytes())
            need(raw == payloads[name], "Reconstructed numeral differs: " + name)
        original = json.loads((recipe / "COEFFICIENT_BINDING.json").read_text())
        for key in ["geometry", "padding_controller", "transition_json_sha256"]:
            need(generated[key] == original[key], "Finite native certificate: " + key)
    result = {
        "status": "PASS",
        "fixed_tuple": "source44 compact, all four ports together",
        "literal_polynomial_sha256": binding["polynomial_sha256"],
        "raw_bytes_reconstructed": sum(map(len, payloads.values())),
        "all_four_numerals_identical": True,
        "fixed_congruence_and_mask_bounds": True,
        "finite_geometry_and_padding_certificates_match": True,
        "scope": "Exact finite numeral/data checks; not a verification of the unbounded native theorem.",
    }
    (HERE / "COEFFICIENT_VERIFICATION.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
