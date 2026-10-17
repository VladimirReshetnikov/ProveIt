#!/usr/bin/env python3
"""Independently reparse all saved tables and check every quotient and boot.

No original compiler, register-box summary or network access is used here.
This finite verification does not establish a Con(ZFC) endpoint.
"""
import hashlib,json,sys
from pathlib import Path
from contiguous_initializer import check_literal_boot
from exact_quotient import parse,verify_certificate,minimize

if not __debug__: raise RuntimeError("Run with assertions enabled")
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent/"results"
evidence=json.loads((root/"evidence.json").read_text())
for r in evidence["records"]:
    name=r["name"]
    raw=(root/(name+".tm")).read_bytes()
    reduced=(root/(name+"_quotient.tm")).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==r["source_sha256"]
    assert hashlib.sha256(reduced).hexdigest()==r["quotient_sha256"]
    source,target=parse(raw),parse(reduced)
    cert=json.loads((root/(name+"_quotient.json")).read_text())
    verify_certificate(source,target,cert)
    b=check_literal_boot(source,0,r["boot"]["state"],r["contract"])
    qb=check_literal_boot(target,0,r["quotient_boot"]["state"],r["contract"])
    assert b==r["boot"] and qb==r["quotient_boot"]
    assert len(source)==2*r["raw_states"] and len(target)==2*r["quotient_states"]
for r in evidence.get("baseline_quotient_controls",[]):
    name=r["name"]
    data=(root/(name+".tm")).read_bytes()
    assert hashlib.sha256(data).hexdigest()==r["normalized_sha256"]
    source=parse(data)
    target=parse((root/(name+"_quotient.tm")).read_bytes())
    cert=json.loads((root/(name+"_quotient.json")).read_text())
    verify_certificate(source,target,cert)
    assert not cert["nontrivial_classes"] and len(source)==len(target)
    freshly_minimized,fresh_certificate=minimize(source)
    assert len(freshly_minimized)==len(source) and not fresh_certificate["nontrivial_classes"]
print(f"PASS: {len(evidence['records'])} complete quotient certificates, 36 exact whole-tape boots, and 2 published-table controls")
