#!/usr/bin/env python3
"""Validate the standalone coefficient compiler against pinned source.

The reference's two inspected compile_windows function ASTs are extracted
without importing or executing either historical module or test suite.
They receive minimal arithmetic/container dependencies. Five fixtures cover
both high-monomial branches, padded layouts, and multiple alphabets. The
smallest fixture additionally materializes all constants and checks the
shifted MF alias and modular evaluation. No claim is made to have enumerated
the actual K215 window alphabet or its enormous numeral expansions.
"""
from __future__ import annotations

import ast
import hashlib
from itertools import product
import json
from pathlib import Path
from types import SimpleNamespace

from fixed_compiler import compile_windows, next_five_power, add_term, require

HERE = Path(__file__).resolve().parent
REFERENCE76 = HERE / "explore_fixed_raw_universal_76.py"
REFERENCE75 = HERE / "complete75_half_binomial_compiler.py"


def extracted_function(path, name, environment):
    tree = ast.parse(path.read_text())
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name]
    require(len(functions) == 1, "reference function not found uniquely")
    isolated = ast.Module(body=functions, type_ignores=[])
    namespace = dict(environment)
    exec(compile(ast.fix_missing_locations(isolated), str(path), "exec"), namespace)
    return namespace[name]


FIELD_NAMES = ("windows a A coeff mu padding m positions payload dummy anchors "
               "anchor_unit H T1 T2 L R radix_bits d DCpoly MFpoly").split()


class ReferenceRecord:
    def __init__(self, *args):
        require(len(args) == len(FIELD_NAMES), "reference constructor mismatch")
        self.__dict__.update(zip(FIELD_NAMES, args))


def is_five_power(n):
    if n < 1:
        return False
    while n % 5 == 0:
        n //= 5
    return n == 1


def run():
    compile76 = extracted_function(REFERENCE76, "compile_windows", {
        "product": product, "next_five_power": next_five_power,
        "is_five_power": is_five_power, "Compiled": ReferenceRecord,
        "previous": SimpleNamespace(previous=SimpleNamespace(add_term=add_term)),
    })
    compile75 = extracted_function(REFERENCE75, "compile_windows", {
        "baseline": SimpleNamespace(compile_windows=compile76,
                                    next_five_power=next_five_power),
    })
    cycle = [1, 0, 0]
    windows3 = [tuple(cycle[(i-dx-dy) % 3] for dy in (-1,0,1) for dx in (-1,0,1))
                for i in range(3)]
    fixtures = [([(0,)*9,(1,)*9],2), (windows3,2),
                (list(product(range(2),repeat=9))[:100],2),
                ([(0,)*9,(1,)*9,(2,)*9],3),
                (list(product(range(2),repeat=9))[:3],2)]
    records = []
    for windows, a in fixtures:
        original, fresh = compile75(windows, a), compile_windows(windows, a)
        for field, value in original.__dict__.items():
            if field == "unshifted_mass_bound":
                require(value == (len(fresh.positions)+2)*(2*sum(fresh.coeff.values())+6), field)
            else:
                require(getattr(fresh, field) == value, f"reference mismatch: {field}")
        records.append({"windows": len(windows), "alphabet": a,
                        "high_correction": fresh.high_correction,
                        "inner_bits": fresh.radix_bits, "cell_bits": fresh.d,
                        "all_reference_fields_equal": True,
                        "constants_mod_1000000007": fresh.constants_mod(1000000007)})
    require({r["high_correction"] for r in records} == {0,1}, "missing correction branch")
    first = compile_windows(*fixtures[0])
    exact = first.materialize(max_bits=25_000_000)
    for modulus in (4,5,8,9,17,1000000007):
        residue = first.constants_mod(modulus)
        require(residue == {k: v % modulus for k, v in exact.items()}, "modular export mismatch")
    require(exact["MF"] == exact["MF_native"] + exact["B"] - 1, "shifted mask alias")
    require(exact["Kconstant"] == exact["DC"] + exact["B"]*exact["DR"], "transport alias")
    require(exact["W0"] == 1 << (first.radix_bits + 2*first.d), "fixed marker constant")
    rejected = 0
    for w, a in [([],2), ([(0,)*9,(0,)*9],2), ([(0,)*9,(2,)*9],2),
                  ([(0,)*8,(1,)*9],2), ([(0,)*9,(True,)*9],2)]:
        try:
            compile_windows(w,a)
        except ValueError:
            rejected += 1
    require(rejected == 5, "malformed window accepted")
    return {"status": "PASS", "snapshot": "cdd582bec13f908df3711fa9e05d1ddac368a5db",
            "reference_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in (REFERENCE76,REFERENCE75)},
            "fixtures": records, "reference_function_equivalence_fixtures": len(records),
            "fully_materialized_small_fixture": True,
            "materialized_small_fixture_W0_bit_length": exact["W0"].bit_length(),
            "modular_exports_checked": 6, "malformed_inputs_rejected": rejected,
            "K215_window_alphabet_enumerated": False,
            "K215_numerals_materialized": False}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
