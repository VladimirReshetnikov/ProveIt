#!/usr/bin/env python3
"""Oracle-check discovery statuses and replay with the producer disabled.

Mutation tests alter assertions so that the modified certificate is false;
mere harmless changes such as enlarging a witness sector are not rejected
requirements. The expected geometric status is taken from Regina's complete
vertex lists, never from the sector implementation.
"""

from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
from copy import deepcopy
import hashlib
import importlib
import inspect
import json
from pathlib import Path
import sys
import time


@contextmanager
def producer_disabled(producer):
    saved = {name:value for name,value in vars(producer).items()
             if inspect.isfunction(value) and value.__module__ == producer.__name__}

    def disabled(*args,**kwargs):
        raise AssertionError("sector producer called during independent replay")

    try:
        for name in saved:
            setattr(producer,name,disabled)
        yield len(saved)
    finally:
        for name,value in saved.items():
            setattr(producer,name,value)


def selected_cases(cases,fixtures):
    selected = {i for i,c in enumerate(cases) if c["selection"]=="exhaustive_small"}
    for name,fixture in fixtures.items():
        if fixture["tetrahedra"]<=3:
            continue
        local = [(i,c) for i,c in enumerate(cases) if c["fixture_id"]==name]
        for predicate in [
            lambda c: bool(c["standard_essential_disc_indices"]),
            lambda c: c["standard_positive_euler_exists"] and not c["standard_essential_disc_indices"],
            lambda c: c["kernel_dimension"]==3,
            lambda c: not c["standard_positive_euler_exists"] and bool(c["quad_indices"]),
        ]:
            eligible = [(i,c) for i,c in local if predicate(c)]
            if eligible:
                selected.add(max(eligible,key=lambda x:len(x[1]["standard_indices"]))[0])
    # Explicit isolated RP2 and boundary-parallel-disc guard sectors.
    for i,c in enumerate(cases):
        if c["fixture_id"] in ["solid_torus_sum_rp3","solid_torus_sum_s2xs1"]:
            if sum(q>=0 for q in c["types"])==1:
                selected.add(i)
    return sorted(selected)


def expected_status(fixture,case,phase):
    collection = "quad_vertices" if phase=="quadrilateral" else "standard_vertices"
    indices = case["quad_indices"] if phase=="quadrilateral" else case["standard_indices"]
    surfaces = [fixture[collection][i] for i in indices]
    if any(s["essential_disc"] for s in surfaces):
        return "DISC_FOUND"
    if not any(s["euler_characteristic"]>0 for s in surfaces):
        return "NO_POSITIVE_EULER"
    return "POSITIVE_EULER_ONLY" if phase=="quadrilateral" else "NO_VERTEX_DISC_IN_SECTOR"


def mutations(triangulation,certificate):
    source = deepcopy(triangulation)
    for row in source["tetrahedra"]:
        target = next((target for target in row if target is not None),None)
        if target is not None:
            target["permutation"][0],target["permutation"][1] = (
                target["permutation"][1],target["permutation"][0])
            break
    yield "changed_source_gluing",source,deepcopy(certificate)
    proof = deepcopy(certificate); proof["source_sha256"]="0"*64
    yield "source_digest",triangulation,proof
    proof = deepcopy(certificate); proof["schema"]="not-a-sector-certificate"
    yield "schema",triangulation,proof
    proof = deepcopy(certificate); proof["allowed_types"]=[[0,0],[0,1]]
    yield "overlapping_support",triangulation,proof
    if certificate["schema"]=="normal-sector-witness-v1":
        proof = deepcopy(certificate)
        proof["coordinates"][0][0] += 1
        yield "witness_coordinates",triangulation,proof
        proof = deepcopy(certificate); proof["allowed_types"]=[]
        yield "witness_excluded_quadrilaterals",triangulation,proof
        proof = deepcopy(certificate); proof["disk_certificate"]["compressing_disk_components"]=0
        yield "witness_disc_count",triangulation,proof
        proof = deepcopy(certificate); del proof["disk_certificate"]
        yield "missing_witness_disc_proof",triangulation,proof
    else:
        proof = deepcopy(certificate); proof["phase"]="invalid"
        yield "phase",triangulation,proof
        proof = deepcopy(certificate); proof["status"]="DISC_FOUND"
        yield "exhaustion_status",triangulation,proof
        if certificate["rays"]:
            proof = deepcopy(certificate); proof["rays"].pop()
            yield "missing_ray",triangulation,proof
            proof = deepcopy(certificate); proof["rays"].append(deepcopy(proof["rays"][0]))
            yield "duplicate_ray",triangulation,proof
            proof = deepcopy(certificate); proof["rays"][0]["euler_characteristic"] += 1
            yield "euler_characteristic",triangulation,proof
            proof = deepcopy(certificate); proof["rays"][0]["quadrilaterals"][0] += 1
            yield "ray_coordinates",triangulation,proof
        positive = next((i for i,r in enumerate(certificate["rays"])
                         if r["euler_characteristic"]>0),None)
        if positive is not None:
            proof = deepcopy(certificate)
            proof["rays"][positive]["disk_certificate"]["compressing_disk_components"]=1
            yield "negative_disc_count",triangulation,proof
            proof = deepcopy(certificate); del proof["rays"][positive]["disk_certificate"]
            yield "missing_negative_disc_proof",triangulation,proof


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fast",type=Path,required=True)
    ap.add_argument("--corpus",type=Path,default=Path(__file__).with_name("discovery_corpus.json"))
    ap.add_argument("--cases",type=Path,default=Path(__file__).with_name("sector_cases.json"))
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("sector_certificate_audit.json"))
    args = ap.parse_args()
    sys.path.insert(0,str(args.fast.resolve()))
    producer = importlib.import_module("fastunknot.normal_sector")
    verifier = importlib.import_module("fastunknot.normal_sector_verify")
    corpus = json.loads(args.corpus.read_text())
    cases_data = json.loads(args.cases.read_text())
    assert hashlib.sha256(args.corpus.read_bytes()).hexdigest() == cases_data["corpus_sha256"]
    cases = cases_data["cases"]
    fixtures = {r["id"]:r for r in corpus["records"]}
    selected = selected_cases(cases,fixtures)
    result = {
        "schema":"normal-sector-certificate-audit-v1",
        "source_sha256":{
            "producer":hashlib.sha256(Path(producer.__file__).read_bytes()).hexdigest(),
            "verifier":hashlib.sha256(Path(verifier.__file__).read_bytes()).hexdigest(),
            "audit":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
        "corpus_sha256":cases_data["corpus_sha256"],
        "cases_sha256":hashlib.sha256(args.cases.read_bytes()).hexdigest(),
        "records":[],"certificates":{},"mutations":[],"allowance_checks":[],
        "callback_checks":[],
    }
    status_counts = Counter()
    sample_certificates = {}
    start = time.perf_counter()
    for position,index in enumerate(selected):
        case = cases[index]
        fixture = fixtures[case["fixture_id"]]
        allowed = [[i,q] for i,q in enumerate(case["types"]) if q>=0]
        for phase in ["quadrilateral","standard"]:
            expected = expected_status(fixture,case,phase)
            answer = producer.discover_in_sector(fixture["triangulation"],allowed,phase=phase)
            assert answer["status"] == expected,(index,phase,expected,answer["status"])
            proof = answer["certificate"]
            encoded = json.dumps(proof,sort_keys=True,separators=(",",":"))
            digest = hashlib.sha256(encoded.encode()).hexdigest()
            replay = verifier.verify_sector_witness if expected=="DISC_FOUND" else verifier.verify_sector_exhaustion
            with producer_disabled(producer) as disabled_count:
                assert replay(fixture["triangulation"],proof),(index,phase,"replay failed")
            result["certificates"][digest]=proof
            result["records"].append({"case_index":index,"fixture_id":case["fixture_id"],
                "phase":phase,"status":expected,"certificate_sha256":digest,
                "producer_functions_disabled_during_replay":disabled_count,
                "replay_accepted":True})
            status_counts[expected]+=1
            key = (phase,expected)
            if proof.get("rays") or expected=="DISC_FOUND":
                sample_certificates.setdefault(key,(fixture["triangulation"],proof,replay))
        if position%50==0:
            print(position,"of",len(selected),"elapsed",round(time.perf_counter()-start,2),flush=True)
    for (phase,status),(triangulation,proof,replay) in sample_certificates.items():
        for name,source,changed in mutations(triangulation,proof):
            with producer_disabled(producer):
                accepted = replay(source,changed)
            assert accepted is False,(phase,status,name,"bad mutation accepted")
            result["mutations"].append({"phase":phase,"status":status,
                "mutation":name,"rejected":True})
    fixture = fixtures["fibonacci_lst_01"]
    for parameters,expected in [
        ({"max_bases":0},"INCONCLUSIVE"),
        ({"max_orbit_cycles":0},"INCONCLUSIVE"),
    ]:
        answer = producer.discover_in_sector(fixture["triangulation"],[[0,2]],**parameters)
        assert answer["status"]==expected and "certificate" not in answer
        result["allowance_checks"].append({"parameters":parameters,"status":answer["status"],
                                           "certificate_absent":True})
    answer = producer.discover_in_sector(fixture["triangulation"],[],max_bases=0)
    assert answer["status"]=="NO_POSITIVE_EULER"
    with producer_disabled(producer):
        assert verifier.verify_sector_exhaustion(fixture["triangulation"],answer["certificate"])
    result["allowance_checks"].append({"parameters":{"empty_sector":True,"max_bases":0},
        "status":answer["status"],"replay_accepted":True})

    class FalseValuedCallback:
        def __init__(self,stop):
            self.calls=0
            self.stop=stop

        def __bool__(self):
            return False

        def __call__(self):
            self.calls+=1
            if self.calls==self.stop:
                raise ValueError("audit callback cancellation")

    for wanted in ["normal-sector-witness-v1","normal-sector-exhaustion-v1"]:
        triangulation,proof,replay=next(value for value in sample_certificates.values()
                                       if value[1]["schema"]==wanted)
        for stop in [2,4]:
            callback=FalseValuedCallback(stop)
            with producer_disabled(producer):
                try:
                    replay(triangulation,proof,check=callback)
                except ValueError as exc:
                    assert str(exc)=="audit callback cancellation"
                else:
                    raise AssertionError("ValueError callback was swallowed")
            assert callback.calls==stop
            result["callback_checks"].append({"schema":wanted,
                "false_valued_callable":True,"calls_before_ValueError":stop,
                "ValueError_propagated":True})
    result["summary"]={"sectors":len(selected),"certificate_replays":len(result["records"]),
        "all_statuses_match_regina":True,"status_counts":dict(status_counts),
        "mutation_rejections":len(result["mutations"]),
        "allowance_checks":len(result["allowance_checks"]),
        "callback_checks":len(result["callback_checks"]),
        "wall_seconds":time.perf_counter()-start}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result["summary"],indent=2))


if __name__ == "__main__":
    main()
