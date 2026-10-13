#!/usr/bin/env python3
"""Reproduce the sixteen packet-loader and verifier-dispatch boundary checks."""

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


PACKAGE = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-root", type=Path, required=True)
    parser.add_argument("--target", type=Path,
                        default=PACKAGE / "certificates" / "figure_eight.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    fast = args.fast_root.expanduser().resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import encoded_integer
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

    spec = importlib.util.spec_from_file_location(
        "delivered_verify_packets", PACKAGE / "tools" / "verify_packets.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    source, certificate, target_hash = module.read_packet(args.target, encoded_integer)
    original = dict(id=source["id"], triangulation=source["triangulation"],
                    coordinates=source["coordinates"],
                    result=dict(status="COMPLETE", certificate=certificate))
    records = []
    with tempfile.TemporaryDirectory(prefix="euler_packet_review_") as temp:
        packet_path = Path(temp) / "packet.json"

        def rejected(name, raw):
            packet_path.write_text(raw, encoding="utf-8")
            try:
                module.read_packet(packet_path, encoded_integer)
            except (ValueError, TypeError) as exc:
                records.append(dict(name=name, passed=True,
                                    exception=type(exc).__name__, detail=str(exc)))
            else:
                raise AssertionError(name + " was accepted")

        raw = json.dumps(original)
        rejected("duplicate_object_key", raw[:-1] + ',"id":"duplicate"}')
        for name, value in [("floating_coordinate", 1.0),
                            ("boolean_coordinate", True),
                            ("decimal_string_coordinate", "1")]:
            data = copy.deepcopy(original)
            data["coordinates"][0][0] = value
            rejected(name, json.dumps(data))
        for name, value in [("NaN", float("nan")),
                            ("positive_infinity", float("inf")),
                            ("negative_infinity", -float("inf"))]:
            data = copy.deepcopy(original)
            data["result"]["invalid_metadata"] = value
            rejected(name, json.dumps(data))
        data = copy.deepcopy(original)
        data["certificate"] = data["result"]["certificate"]
        rejected("ambiguous_layout", json.dumps(data))
        rejected("non_object_packet", "[]")
        data = copy.deepcopy(original)
        data["coordinates"][0].pop()
        rejected("wrong_coordinate_row_size", json.dumps(data))
        data = copy.deepcopy(original)
        data["id"] = False
        rejected("boolean_source_identifier", json.dumps(data))
        data = copy.deepcopy(original)
        data["result"].pop("certificate")
        rejected("missing_certificate", json.dumps(data))

        data = copy.deepcopy(original)
        data["coordinates"] = [[hex(encoded_integer(x)) for x in row]
                               for row in data["coordinates"]]
        packet_path.write_text(json.dumps(data), encoding="utf-8")
        source, proof, _ = module.read_packet(packet_path, encoded_integer)
        if verify_normal_cut_handlebodies(
                source["triangulation"], source["coordinates"], proof) is not True:
            raise AssertionError("explicit hexadecimal source did not replay")
        records.append(dict(name="hexadecimal_source_replays", passed=True))
        if verify_normal_cut_handlebodies(source["triangulation"],
                source["coordinates"], proof, max_operations=0) is not False:
            raise AssertionError("zero operation cap did not reject this target")
        records.append(dict(name="zero_operation_cap_rejects", passed=True))

        data = copy.deepcopy(original)
        data["result"]["certificate"]["census"]["free_rank_sum"] = True
        packet_path.write_text(json.dumps(data), encoding="utf-8")
        source, proof, _ = module.read_packet(packet_path, encoded_integer)
        if verify_normal_cut_handlebodies(
                source["triangulation"], source["coordinates"], proof) is not False:
            raise AssertionError("boolean census rank accepted")
        records.append(dict(name="boolean_certificate_rank_rejects", passed=True))

        data = copy.deepcopy(original)
        data["coordinates"][0][0] = 1.0
        packet_path.write_text(json.dumps(data), encoding="utf-8")
        report_path = Path(temp) / "report.json"
        run = subprocess.run([sys.executable, str(PACKAGE / "tools" / "verify_packets.py"),
                              "--fast-root", str(fast), "--packets", str(packet_path),
                              "--output", str(report_path)], capture_output=True, text=True)
        report = json.loads(report_path.read_text())
        if run.returncode != 1 or report["passed"] is not False or report["verified"] != 0:
            raise AssertionError("malformed CLI packet did not fail with report")
        records.append(dict(name="malformed_cli_nonzero_exit", passed=True,
                            exit_code=run.returncode))

    result = dict(passed=True, checks=len(records), target_sha256=target_hash,
                  scope="Dispatcher adapter and transport boundary checks; no producer or benchmark invoked.",
                  records=records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(dict(passed=True, checks=len(records))))


if __name__ == "__main__":
    main()
