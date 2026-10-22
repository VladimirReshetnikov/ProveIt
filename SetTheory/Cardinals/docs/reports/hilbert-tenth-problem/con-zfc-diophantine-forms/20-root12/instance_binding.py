"""One complete, immutable numeric tuple for every main polynomial packet."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
TUPLE_ID="T4-4094-binary-copy-zero-padding-5pow11"
TUPLE_SHA256="726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938"
ALIASES={"Bm1":"beta","beta":"beta","Kconstant":"K","K0":"K","K":"K","MC":"MC","MF":"MF_source","MF_source":"MF_source"}
def binding(ports):
    spec=json.loads((ROOT/"coefficients/COEFFICIENTS.json").read_text())
    if spec["tuple_id"]!=TUPLE_ID or spec["tuple_sha256"]!=TUPLE_SHA256:
        raise ValueError("Unexpected coefficient tuple")
    aliases={name:ALIASES[name] for name in ports}
    if list(aliases.values())!=spec["polynomial_ports"]:
        raise ValueError("All four coefficient ports must be supplied in canonical order")
    return {"tuple_id":TUPLE_ID,"tuple_sha256":TUPLE_SHA256,
            "recipe":"../coefficients/COEFFICIENTS.json",
            "aliases":aliases,"numeric_encoding":spec["numeric_encoding"],
            "numeric_coefficients":{name:{**spec["numeric_coefficients"][name],"file":"../coefficients/"+spec["numeric_coefficients"][name]["file"]} for name in spec["polynomial_ports"]},
            "transfer_proof":"../coefficients/COEFFICIENT_PROOF.md",
            "note":"Whole-tuple substitution only; MF denotes the shifted source port, never the unshifted native mask."}
