#!/usr/bin/env python3
"""Rebuild small explicit certificates and audit the sparse construction."""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import copy
import json
import random

from sparse_mass import (Builder, LocalTable, Poly, compile_history,
                         compile_morita_inputs, physical_inverse, physical_step,
                         records_to_config, unit_records, verify_bound_export,
                         verify_export)


HERE = Path(__file__).resolve().parent


def all_binary_permutations():
    fibers = defaultdict(list)
    for triple in product(range(2), repeat=3):
        fibers[sum(triple)].append(triple)
    for choices in product(*(list(permutations(fibers[s])) for s in sorted(fibers))):
        mapping = {}
        for s, targets in zip(sorted(fibers), choices):
            mapping.update(zip(fibers[s], targets))
        yield LocalTable.from_mapping(1, mapping)


def random_table(K, rng):
    fibers = defaultdict(list)
    for triple in product(range(K+1), repeat=3):
        fibers[sum(triple)].append(triple)
    mapping = {}
    for triples in fibers.values():
        targets = triples[:]
        rng.shuffle(targets)
        mapping.update(zip(triples, targets))
    return LocalTable.from_mapping(K, mapping)


def check_case(table, configuration, T, orthant=False):
    b, metadata = compile_history(table, configuration, T, orthant_exact=orthant)
    assert b.validate_witness()
    assert max(b.values, default=0) <= metadata["witness_height_bound"]
    M, q = metadata["M"], table.K+1
    assert len(b.values) == T*(M*(q**3+14)+5*M*(M-1))
    assert len(b.residuals) == T*(17*M+5*M*(M-1)+2*M*orthant)
    trajectory = b.decode(metadata["physical_shift"])
    expected = configuration
    for t in range(T+1):
        assert trajectory[t] == expected
        if t < T:
            after = physical_step(table, expected)
            assert sum(map(sum, after.values())) == M
            if table.reversible:
                assert physical_inverse(table, after) == expected
            expected = after
    return b, metadata


def reject(function):
    try:
        function()
    except (ValueError, TypeError):
        return
    raise AssertionError("malformed input was accepted")


def main():
    results = {"status": "passed", "seed": 20261002}
    rng = random.Random(results["seed"])
    tables = list(all_binary_permutations())
    assert len(tables) == 36
    cases = 0
    configs = [
        {0:(1,0,0)},
        {0:(0,1,0)},
        {0:(0,0,1)},
        {-1:(0,0,1), 0:(0,1,0), 1:(1,0,0)},
        {0:(1,1,1)},
        {-10**30:(1,0,0), 10**30:(0,0,1)},
    ]
    for table in tables:
        for configuration in configs:
            for orthant in (False, True):
                check_case(table, configuration, 3, orthant)
                cases += 1
    results["binary_tables"] = len(tables)
    results["binary_history_cases"] = cases

    for _ in range(40):
        table = random_table(2, rng)
        configuration = {}
        for x in rng.sample(range(-5,6), 3):
            triple = tuple(rng.randrange(3) for _ in range(3))
            if sum(triple):
                configuration[x] = triple
        if configuration:
            check_case(table, configuration, 2, bool(rng.randrange(2)))
    results["ternary_random_histories"] = 40

    table = tables[17]
    initial = {-1:(0,0,1), 0:(0,1,0), 1:(1,0,0)}
    b, metadata = check_case(table, initial, 3)
    terminal = b.decode(metadata["physical_shift"])[-1]
    yes, yesmeta = compile_history(table, initial, 3, endpoint=terminal)
    assert yes.validate_witness()
    no, nometa = compile_history(table, initial, 3, endpoint={100:(1,1,1)})
    assert not no.validate_witness()
    assert no.score() > 0
    badmass, _ = compile_history(table, initial, 3, endpoint={0:(1,0,0)})
    assert not badmass.validate_witness()
    results["endpoint_positive_negative_mass_cases"] = 3

    # Every single-coordinate +/-1 mutation is rejected by the actual residuals.
    mutated = 0
    for i, old in enumerate(b.values):
        for new in (old-1, old+1):
            if new < 0:
                continue
            witness = b.values[:]
            witness[i] = new
            assert not b.validate_witness(witness)
            mutated += 1
    results["single_witness_mutations_rejected"] = mutated

    fixtures = HERE / "fixtures"
    fixtures.mkdir(exist_ok=True)
    exports = []
    specifications = [
        ("binary_three_way_collision", table, initial, 3, False),
        ("binary_three_way_collision_orthant", table, initial, 3, True),
        ("huge_empty_span", tables[0], {0:(1,0,0), 10**100:(0,0,1)}, 2, False),
        ("ternary_mixed_mass", random_table(2,rng), {0:(1,1,0), 2:(2,0,1)}, 2, False),
    ]
    for name, table, configuration, T, orthant in specifications:
        b, metadata = check_case(table, configuration, T, orthant)
        path = fixtures / (name+".json")
        payload = b.export(path, metadata)
        replay = verify_bound_export(path)
        assert replay["valid"]
        exports.append({"name": name, **payload["counts"], "bytes": path.stat().st_size,
                        "max_witness_bits": max((x.bit_length() for x in b.values), default=0)})
    results["exports"] = exports

    # Export-level alterations, including metadata that changes semantic input.
    source = json.loads((fixtures / "binary_three_way_collision.json").read_text())
    corruptions = []
    changed = copy.deepcopy(source); changed["witness_values"][0] += 1
    corruptions.append(("witness", changed, False))
    changed = copy.deepcopy(source); changed["metadata"]["initial_configuration"][0][0] -= 1
    corruptions.append(("input_binding", changed, True))
    changed = copy.deepcopy(source); changed["residuals"][0] = []
    corruptions.append(("deleted_constraint", changed, True))
    changed = copy.deepcopy(source); changed["rows"][-1][0][0] = [[[], 100000]]
    corruptions.append(("decoder_alias", changed, True))
    changed = copy.deepcopy(source); changed["witness_values"][0] = True
    corruptions.append(("bool_scalar", changed, True))
    changed = copy.deepcopy(source); changed["parameter_values"] = [0]
    corruptions.append(("extra_parameter", changed, True))
    changed = copy.deepcopy(source); changed["counts"]["literal_multiplications"] += 1
    corruptions.append(("accounting", changed, True))
    changed = copy.deepcopy(source); changed["polynomial"] = "zero"
    corruptions.append(("polynomial_declaration", changed, True))
    temp = HERE / "mutated_export.tmp.json"
    for name, payload, raises in corruptions:
        temp.write_text(json.dumps(payload))
        if raises:
            reject(lambda: verify_bound_export(temp))
        else:
            assert not verify_bound_export(temp)["valid"]
    temp.unlink()
    results["export_mutations_rejected"] = [name for name, _, _ in corruptions]

    # Exhaustive comparison/equality gate semantics and unique tie branch.
    comparisons = 0
    for x, y in product(range(8), repeat=2):
        c = Builder()
        eq = c.eq("test", x, y)
        assert c.value(eq) == int(x == y)
        assert c.validate_witness()
        solutions = []
        # Compare each two-witness gadget independently to keep exhaustive range small.
        for offset in (0,2):
            found = []
            for bit, gap in product(range(2), range(10)):
                w = c.values[:]; w[offset:offset+2] = [bit,gap]
                if all(r.evaluate(w) == 0 for r in c.residuals[offset:offset+2]):
                    found.append((bit,gap))
            assert found == [tuple(c.values[offset:offset+2])]
            comparisons += 1
    results["exhaustive_comparisons"] = comparisons

    # Generic theorem needs conservation, not injectivity. Nonreversible example.
    irreversible = {}
    for key in product(range(2), repeat=3):
        total = sum(key)
        irreversible[key] = tuple(int(i < total) for i in range(3))
    irreversible = LocalTable.from_mapping(1, irreversible)
    assert not irreversible.reversible
    check_case(irreversible, {0:(0,0,1),2:(1,0,0)}, 3)
    reject(lambda: physical_inverse(irreversible,{0:(1,0,0)}))
    results["nonreversible_conservative_case"] = True
    # The first, factorized backend remains only as a labeled cross-check.
    for table in tables[:6]:
        old, oldmeta=compile_history(table,initial,2,lookup_backend="factorized")
        new, newmeta=compile_history(table,initial,2)
        assert old.validate_witness() and new.validate_witness()
        assert old.decode(oldmeta["physical_shift"]) == new.decode(newmeta["physical_shift"])
    results["legacy_factorized_crosschecks"] = 6

    # Paid uniform loader at T=0 avoids enormous unoptimized q^3 full-history exports.
    K, m = 20, 2
    passive = LocalTable.from_mapping(K, {key:key for key in product(range(K+1), repeat=3)})
    loader = []
    for gamma, inc in ((0,None),(2,0),(4,None),(6,1),(7,None)):
        for n0,n1 in ((0,0),(0,1),(1,0),(1,1),(2,5),(10**100,3)):
            b,metadata = compile_morita_inputs(passive,m,gamma,inc,n0,n1,0)
            assert b.validate_witness()
            M=m+19
            assert len(b.values)==len(b.residuals)==4+3*M*(M-1)
            record = b.decode(0)[0]
            assert sum(map(sum,record.values())) == M
            assert max(b.values) <= metadata["witness_height_bound"]
            loader.append((gamma,inc,n0,n1))
    results["uniform_loader_cases_T0"] = len(loader)
    # Polynomial structure does not depend on the actual n0,n1 values.
    a,_=compile_morita_inputs(passive,m,2,0,0,0,0)
    b,_=compile_morita_inputs(passive,m,2,0,10**100,3,0)
    assert a.residuals == b.residuals and a.rows == b.rows
    assert not a.validate_witness(parameters=(1,0))
    results["uniform_loader_parameter_binding"] = True

    # Exact-type checks on external APIs; Python bool must not masquerade as int.
    reject(lambda: compile_history(tables[0],{0:(True,0,0)},1))
    reject(lambda: compile_history(tables[0],{0:(1,0,0)},True))
    reject(lambda: compile_history(tables[0],{False:(1,0,0)},1))
    reject(lambda: compile_history(tables[0],{0:(2,0,0)},1))
    reject(lambda: compile_history(tables[0],{},1))
    reject(lambda: LocalTable.from_mapping(True,{}))
    results["malformed_input_cases_rejected"] = 6

    output=HERE/"check_results.json"
    output.write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
