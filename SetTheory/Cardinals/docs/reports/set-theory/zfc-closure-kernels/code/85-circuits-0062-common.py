"""Portable paths and input loading for Context246 runtime experiments."""
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

PACKAGE = Path(__file__).resolve().parents[2]
BASE = PACKAGE / 'reference/context246'
CERTIFICATE = PACKAGE / 'reference/guard-invariant/product-invariant.json'
OUTPUT = PACKAGE / 'verification/runtime'
LAYOUTS = ('baseline', '0', '233', '235', '236', '237')
EXCLUDED = (8202, 8203, 8204, 8358, 8359, 8360)
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


L = load_module('runtime_literal_reference', BASE / 'code/check_literal_instructions.py')


def inputs(layout):
    layout = str(layout).removeprefix('layout')
    if layout == 'baseline':
        sites = L.program_sites(BASE / 'sources/Prog254.v')
        path = BASE / 'machine/zfc_prefix246_old.tm'
    else:
        assert layout in LAYOUTS[1:]
        directory = PACKAGE / 'candidates' / ('layout' + layout)
        sites = json.loads((directory / 'program.json').read_text())['sites']
        path = directory / 'machine_old.tm'
    table = L.read_table(path)
    states = {q for q, bit in table}
    assert len(sites) == 6460 and len(states) == 246 and len(table) == 492
    assert {target for write, direction, target in table.values()} <= states | {254}
    return sites, table


def guarded_sites(sites):
    case = 0
    for site, (pc, op, arg) in enumerate(sites):
        for zero in ((True, False) if op == 'CD' else (None,)):
            yield case, site, pc, op, arg, zero
            case += 1
    assert case == 8391
