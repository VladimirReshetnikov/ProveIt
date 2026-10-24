#!/usr/bin/env python3
"""Replay the saturated-nine finite certificate, without any Lean command.

The copied release verifier is source-pinned and inspected. It independently
checks the builder's literal DAGs and exact polynomial tables. This wrapper
also checks relocation-only circuit changes, full shared payload bytes,
coherent four-port reconstruction of all11 leaves, and unique degree heads.
"""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
SHARED = ROOT.parent / "gap2082-compact54"
ARCHIVE_SHA = "ff9c3bb17a009b2ec11453b840a56aeb34f37144487e89cd65d5e96e5fc48b1c"
VERIFIER_SHA = "392c09833645635a876de8831dff90f80b1f4663cbf01572ebe365d6b4d9f116"
BINDING_SHA = "e8fd5a7e4ced4e298d37a7a07ca89a14474777f61c62afc54318e1ec7edf12fd"
PORT_BINDING_SHA = "d176bcc6bf4b09fda67d9ffc0ced40471b0f72522b0772f06372fc80f20e654c"
CASES = {
    "saturated_positive.json": (434, 1628768, "471fd0276d9335b380d8d493770c7de4a17a26d016acbb3d49ca42055214b59b"),
    "saturated_natural.json": (441, 1628768, "6c6f4db927cf228ec36202f33cc918424f12d1c725b6c79f70c5a0fed60d326c"),
    "saturated_radical_positive.json": (1074, 1103950, "e2247b5082833a41f2e704890c7793ad0933dc9194f77db8d8f55cd8d185c9b1"),
    "saturated_radical_natural.json": (1081, 1103950, "ac2c5a5475dd70bd0f5d020ee21d9dcd781a4e4bc0ef1c22c51e7a0114e293c6"),
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def authenticate():
    pins = json.loads((ROOT / "PINS.json").read_text())
    need(pins["archive_sha256"] == ARCHIVE_SHA, "original archive pin")
    for path, record in pins["files"].items():
        stored = (ROOT / path).read_bytes()
        need(sha(stored) == record["stored_sha256"], "stored source " + path)
        raw = gzip.decompress(stored) if record["encoding"] == "gzip" else stored
        need(sha(raw) == record["raw_sha256"] and len(raw) == record["raw_bytes"], "raw original member " + path)
    need(sha((ROOT / "source/archive_verify.py").read_bytes()) == VERIFIER_SHA, "inspected independent verifier")
    for name, (operations, degree, digest) in CASES.items():
        raw = (ROOT / name).read_bytes()
        body = json.loads(raw)
        need(sha(raw) == pins["circuits"][name]["current_sha256"], "current DAG bytes")
        need(body["total_operations"] == operations and body["exact_degree"] == degree, "endpoint metrics")
        need(body["variables"] == ["b", "g", "h", "s", "w", "C", "i", "j", "n"], "all9 declared inputs")
        need(body["domain"] == ("natural" if "natural" in name else "positive"), "endpoint domain")
        need(body["fixed_binding"] == "../gap2082-compact54/fixed/BINDING.json", "shared payload reference")
        body["fixed_binding"] = "fixed/BINDING.json"
        need(sha(encoded(body)) == digest == pins["circuits"][name]["original_sha256"], "only original binding path changed")
    for domain in ("positive", "natural"):
        raw = (ROOT / "upstream" / ("gap2082_" + domain + ".json")).read_bytes()
        need(raw == (ROOT.parent / "gap2082-shared-products" / ("gap2082_" + domain + ".json")).read_bytes(), "same frozen440/447 parent")
    return pins


def fixed_values():
    raw_binding = (SHARED / "fixed/BINDING.json").read_bytes()
    raw_ports = (SHARED / "coefficients/COEFFICIENT_BINDING.json").read_bytes()
    need(sha(raw_binding) == BINDING_SHA and raw_binding == (ROOT / "source/fixed_binding.json").read_bytes(), "full11-leaf binding bytes")
    need(sha(raw_ports) == PORT_BINDING_SHA and raw_ports == (ROOT / "source/port_binding.json").read_bytes(), "whole four-port binding bytes")
    ports, port_records = {}, []
    for record in json.loads(raw_ports)["ports"]:
        compressed = (SHARED / "coefficients" / record["gzip_file"]).read_bytes()
        raw = gzip.decompress(compressed)
        need(sha(compressed) == record["gzip_sha256"] and sha(raw) == record["sha256"], "whole native port hashes")
        value = int.from_bytes(raw, "little")
        need(len(raw) == record["bytes"] and value.bit_length() == record["bits"] and raw[-1] != 0, "native port dimensions")
        ports[record["port"]] = value
        port_records.append(dict(port=record["port"], raw_bytes=len(raw), sha256=sha(raw)))
    need(set(ports) == {"beta", "K", "MC", "MF_source"}, "whole coherent tuple")
    parent = json.loads((ROOT / "upstream/gap2082_positive.json").read_text())
    ordered = [ports[name] for name in ("beta", "K", "MC", "MF_source")]
    expected = {}
    for recipe in parent["coefficient_recipes"]:
        total = 0
        for term in recipe["terms"]:
            value = term["integer"]
            for port, exponent in zip(ordered, term["port_powers"]):
                value *= port ** exponent
            total += value
        expected[recipe["name"]] = total
    expected["base_scale"] = 1 << parent["base_scale_exponent"]
    expected["threshold_" + str(parent["threshold_scale_exponent"])] = 1 << parent["threshold_scale_exponent"]
    binding = json.loads(raw_binding)
    need(set(expected) == {record["name"] for record in binding["records"]}, "all11 leaves derived from same tuple")
    records = []
    for record in binding["records"]:
        compressed = (SHARED / record["path"]).read_bytes()
        raw = gzip.decompress(compressed)
        need(sha(compressed) == record["gzip_sha256"] and sha(raw) == record["raw_sha256"], "complete fixed payload hashes")
        value = expected[record["name"]]
        need((value > 0) - (value < 0) == record["sign"], "signed fixed leaf")
        need(abs(value).bit_length() == record["bits"] and len(raw) == record["raw_bytes"], "fixed dimensions")
        need(abs(value).to_bytes(len(raw), "little") == raw, "all fixed bytes from coherent ports")
        records.append(dict(name=record["name"], raw_bytes=len(raw), sha256=sha(raw), all_bytes_equal=True))
    for name in CASES:
        body = json.loads((ROOT / name).read_text())
        need(body["coefficient_recipes"] == parent["coefficient_recipes"], "unchanged coefficient recipes")
        need({node["name"] for node in body["nodes"] if node["kind"] == "fixed"} == set(expected), "all and only11 fixed leaves")
    return dict(binding_sha256=BINDING_SHA, port_binding_sha256=PORT_BINDING_SHA,
                coherent_ports=port_records, fixed_leaves=records,
                port_raw_bytes=sum(r["raw_bytes"] for r in port_records),
                fixed_raw_bytes=sum(r["raw_bytes"] for r in records))


def main():
    authenticate()
    spec = importlib.util.spec_from_file_location("saturated_archive_checker", ROOT / "source/archive_verify.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.ROOT = ROOT
    # The large shifted tables are stored compressed without changing their
    # exact original bytes. Only their reader is adapted; no audit is bypassed.
    def readpoly(name, n=4):
        path = ROOT / "source" / name
        raw = path.read_bytes() if path.exists() else gzip.decompress(path.with_name(path.name + ".gz").read_bytes())
        out = {}
        for record in json.loads(raw):
            exponents, coefficient = record["powers"], record["coefficient"]
            need(len(exponents) == n and all(type(x) is int and 0 <= x < checker.BASE for x in exponents), "exact table exponents")
            need(type(coefficient) is int and coefficient != 0, "integer coefficient")
            key = checker.encode(exponents)
            need(key not in out, "unique monomial")
            out[key] = coefficient
        return out
    checker.readpoly = readpoly
    formulas, upper, defect, local = checker.audit_local_tables()
    circuits = checker.audit_circuits(formulas, upper)
    degrees = checker.audit_degrees(upper, defect)
    weights = (18097, 1, 1, 8799)
    def head(poly, powers, coefficient):
        degree = checker.degree(poly, weights)
        leaders = [(checker.powers(e, 4), c) for e, c in poly.items()
                   if sum(x*y for x, y in zip(checker.powers(e, 4), weights)) == degree]
        need(leaders == [(powers, coefficient)], "complete unique positive weighted leader")
        return dict(degree=degree, powers=powers, coefficient=coefficient)
    cheap = checker.times(checker.times(formulas["T"], formulas["G"]), formulas["H"])
    cheap_defect = checker.minus(checker.square(cheap), formulas["raw"])
    heads = dict(cheap=head(cheap, (18,19,5,1), 2**10),
                 cheap_defect=head(cheap_defect, (34,38,10,2), 2**20),
                 radical=head(upper, (18,24,6,1), 2**20),
                 radical_defect=head(defect, (18,48,12,2), 2**41))
    result = dict(status="PASS", archive_sha256=ARCHIVE_SHA,
                  exact_local_tables=local, circuits=circuits, fixed=fixed_values(),
                  degree_certificates=degrees, unique_weighted_heads=heads,
                  natural_translation="All9 positive inputs shifted by1; natural j directly supplies j0. Exact whole-output identity checked.",
                  negative_control="Changed final subtraction to addition; exact norm check rejects.",
                  checker_provenance="Pinned, inspected release verifier independent of its builders, with only compressed-table reading adapted. No claimed independent second implementation.",
                  scope="Finite exact algebra, topology, domains, degree-head and whole-coefficient certificates. New unbounded arithmetic was peer-reviewed in PEER_REVIEW.md; native/compiler and internal-ZFC calibration remain inherited. No Lean invoked.")
    path = ROOT / ("VERIFY.optimized.json" if sys.flags.optimize else "VERIFY.json")
    path.write_bytes(encoded(result))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
