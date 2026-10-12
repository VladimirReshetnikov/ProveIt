#!/usr/bin/env python3
"""Replay saved source-bound handlebody certificates; never run a producer.

The default packet directory is relative to this delivered package.  The
integrated fastunknot source tree must always be selected explicitly.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys


PACKAGE = Path(__file__).resolve().parents[1]


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON object key: " + repr(key))
        result[key] = value
    return result


def _reject_number(value):
    raise ValueError("certificate packets require exact integers, not " + value)


def read_packet(path, encoded_integer):
    """Load either archived packet layout without permissive number coercion."""
    raw = path.read_bytes()
    packet = json.loads(raw, object_pairs_hook=_unique_object,
                        parse_float=_reject_number, parse_constant=_reject_number)
    if type(packet) is not dict:
        raise ValueError("packet must be a JSON object")
    if set(packet) == {"source", "certificate"}:
        source, certificate = packet["source"], packet["certificate"]
        if type(source) is not dict or set(source) != {"id", "triangulation", "coordinates"}:
            raise ValueError("source must contain exactly id, triangulation, coordinates")
    elif set(packet) == {"id", "triangulation", "coordinates", "result"}:
        source = packet
        result = packet["result"]
        if type(result) is not dict or result.get("status") != "COMPLETE":
            raise ValueError("archived producer result must have status COMPLETE")
        certificate = result.get("certificate")
    else:
        raise ValueError("unrecognized or ambiguous source packet layout")
    if type(source["id"]) is not str:
        raise ValueError("source id must be a string")
    if type(certificate) is not dict or type(certificate.get("schema")) is not str:
        raise ValueError("certificate must be an object with a string schema")
    rows = source["coordinates"]
    if type(rows) is not list or any(type(row) is not list or len(row) != 7 for row in rows):
        raise ValueError("source coordinates must have seven entries per row")
    # The established codec accepts exact Python integers and explicit signed
    # hexadecimal strings. It rejects bool, float and decimal strings. Keep the
    # original transport representation for the source verifier to check again.
    for row in rows:
        for value in row:
            encoded_integer(value)
    return source, certificate, hashlib.sha256(raw).hexdigest()


def _nonnegative(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-root", type=Path, required=True,
                        help="integrated directory containing fastunknot/")
    parser.add_argument("--packets", type=Path,
                        default=PACKAGE / "certificates" / "group",
                        help="directory of JSON packets, or one JSON packet")
    parser.add_argument("--output", type=Path,
                        help="optional JSON report; otherwise print the report")
    parser.add_argument("--max-operations", type=_nonnegative,
                        help="verifier's recorded-operation cap per packet")
    args = parser.parse_args()
    fast = args.fast_root.expanduser().resolve()
    if not (fast / "fastunknot" / "normal_cut_handlebodies_verify.py").is_file():
        parser.error("--fast-root must contain fastunknot/normal_cut_handlebodies_verify.py")
    location = args.packets.expanduser().resolve()
    paths = sorted(location.glob("*.json")) if location.is_dir() else [location]
    if not paths or any(not path.is_file() for path in paths):
        parser.error("--packets must name a JSON file or a nonempty JSON packet directory")
    if args.output and args.output.expanduser().resolve() in paths:
        parser.error("--output must not overwrite an input packet")

    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import encoded_integer
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

    records = []
    for path in paths:
        record = {"file": path.name, "verified": False}
        try:
            source, certificate, digest = read_packet(path, encoded_integer)
            record.update(source_id=source["id"], schema=certificate["schema"], sha256=digest)
            record["verified"] = verify_normal_cut_handlebodies(
                source["triangulation"], source["coordinates"], certificate,
                max_operations=args.max_operations) is True
            if not record["verified"]:
                record["error"] = "source certificate replay returned False"
        except Exception as exc:
            # A malformed packet or source is a failed replay, never a census
            # or a negative mathematical verdict. Do not intercept cancellation.
            record["error"] = type(exc).__name__ + ": " + str(exc)
        records.append(record)

    loaded = {}
    for name, module in sorted(sys.modules.items()):
        if name == "fastunknot" or name.startswith("fastunknot."):
            filename = getattr(module, "__file__", None)
            if filename:
                path = Path(filename).resolve()
                try:
                    relative = path.relative_to(fast)
                except ValueError:
                    raise RuntimeError("fastunknot import escaped the selected --fast-root")
                if path.suffix == ".py":
                    loaded[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    report = dict(mode="replay_only", dispatcher="verify_normal_cut_handlebodies",
                  passed=all(row["verified"] for row in records), packets=len(records),
                  verified=sum(row["verified"] for row in records),
                  max_operations=args.max_operations, records=records,
                  loaded_source_sha256=loaded)
    payload = json.dumps(report, indent=2, allow_nan=False) + "\n"
    if args.output:
        output = args.output.expanduser().resolve()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(payload, encoding="utf-8")
        print(json.dumps({key: report[key] for key in ("passed", "packets", "verified")}))
    else:
        print(payload, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
