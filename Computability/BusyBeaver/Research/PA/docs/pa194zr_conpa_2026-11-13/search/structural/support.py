"""Portable binding to the final PA194ZR table and universal source contracts."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'reference_cs'))
import compiler as c
import baseline_tools as b

NATIVE_SHA = '745dd4343d88f6d3458cbde6146cfe360283bc7e8a9113d020eed999b81ad85d'


def load():
    assert __debug__ and not sys.flags.optimize, 'Run without -O'
    table_path = ROOT / 'machine/pa194zr.native.tm'
    assert hashlib.sha256(table_path.read_bytes()).hexdigest() == NATIVE_SHA
    rows = b.read_table(table_path)
    sites_json = json.loads((ROOT / 'source/sites.json').read_text())
    sites = [(tuple(map(int, p)), op, arg) for p, op, arg in sites_json]
    cfg = [tuple(x) for x in json.loads((ROOT / 'source/instructions.json').read_text())]
    assert len(sites) == len(cfg) == 3646
    contracts = []
    for i, code in enumerate(cfg):
        start = c.frame(sites[i][0])
        if code[0] == 'inc':
            _, r, target = code
            end = c.canonical(c.frame(sites[target][0], 0, ('x', 'inc', c.PHYSICAL[r])))
            contracts.append((i, None, start, end))
        elif code[0] == 'dec':
            _, r, zero, positive = code
            contracts.append((i, (c.PHYSICAL[r], True), start,
                              c.canonical(c.frame(sites[zero][0]))))
            contracts.append((i, (c.PHYSICAL[r], False), start,
                              c.canonical(c.frame(sites[positive][0], 1, ('x', 'dec', c.PHYSICAL[r])))))
        elif code[0] == 'jump':
            contracts.append((i, None, start, c.canonical(c.frame(sites[code[1]][0]))))
        else:
            assert code == ('halt',)
            contracts.append((i, None, start, None))
    assert len(contracts) == 4754
    return rows, sites, cfg, contracts
