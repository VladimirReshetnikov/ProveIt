#!/usr/bin/env python3
"""CODE ONLY/HOLD: exact accepted P66 data and new recipe-proof binding."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT/'candidates/one-page-fifteen66'
OUTPUTS = ['polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json','SOURCE_INDEX.json']
SEALS = {'candidates/one-page-fifteen66':'065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424',
         'research/grouped-fixed-coefficient-recipe':'f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594',
         'research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()


def authenticate():
    pins = json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for group in ['external_files','own_core']:
        for name, pin in pins[group].items():
            path = ROOT/name
            raw = path.read_bytes()
            need(not path.is_symlink() and {'bytes':len(raw),'sha256':digest(raw)}==pin, 'reviewed whole input '+name)
    need({p['folder']:p['manifest_sha256'] for p in pins['closed_dependencies']}==SEALS, 'three exact whole contracts')
    for parent in pins['closed_dependencies']:
        folder = ROOT/parent['folder']
        raw = (folder/'MANIFEST.json').read_bytes()
        need(digest(raw)==parent['manifest_sha256'], 'whole accepted parent seal')
        files = json.loads(raw)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(actual==set(files), 'whole accepted parent inventory')
        for name, pin in files.items():
            path = folder/name
            data = path.read_bytes()
            expected = {'bytes':len(data),'sha256':digest(data)} if isinstance(pin,dict) else digest(data)
            need(not path.is_symlink() and pin==expected, 'whole accepted parent member '+name)
    return pins


def prepare():
    # The complete specialized polynomial and coefficient binding stay byte-identical.
    data = {name:(PARENT/name).read_bytes() for name in ['polynomial.json','COEFFICIENT_BINDING.json']}
    calibration = deepcopy(json.loads((PARENT/'CALIBRATION_BINDING.json').read_bytes()))
    calibration['proof_sha256'] = digest((HERE/'PROOF.md').read_bytes())
    data['CALIBRATION_BINDING.json'] = encoded(calibration)
    index = {'schema':'indexed_p66_source_inventory_v1',
             'files':{name:{'bytes':len(raw),'sha256':digest(raw)} for name,raw in data.items()},
             'producer_sha256':digest(Path(__file__).read_bytes()),
             'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes())}
    data['SOURCE_INDEX.json'] = encoded(index)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = authenticate()
    data = prepare()
    for name in OUTPUTS:
        path = HERE/name
        need(not path.is_symlink(), 'no source-output symlink')
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes()==data[name], 'whole deterministic source '+name)
    result = {'status':'PASS','optimized_python':bool(sys.flags.optimize),
              'mode':'pure source check' if args.check else 'exact accepted source materialization',
              'operations':66,'exact_degree':157,'whole_indexed_port_bytes':295388,
              'polynomial_and_coefficient_binding_byte_identical_to_accepted_parent':True,
              'files':{name:{'bytes':len(raw),'sha256':digest(raw)} for name,raw in data.items()},
              'producer_sha256':digest(Path(__file__).read_bytes()),
              'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes()),
              'scope':'Same complete equation and four integers; only the local proof hash and data index are rebound. No recipe, native compiler, TeX or PDF program runs.'}
    raw = encoded(result)
    protected = {(ROOT/name).resolve() for group in ['external_files','own_core'] for name in pins[group]}
    protected |= {(HERE/name).resolve() for name in OUTPUTS+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json','equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']}
    need(args.output.resolve()!=ROOT.parents[1].resolve() and ROOT.parents[1].resolve() not in args.output.resolve().parents,
         'receipt must remain outside the repository')
    need(not args.output.is_symlink() and args.output.resolve() not in protected and
         (not args.output.exists() or args.output.read_bytes()==raw), 'separate fresh or identical receipt')
    if not args.check:
        for name, blob in data.items():
            if not (HERE/name).exists():
                (HERE/name).write_bytes(blob)
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__=='__main__':
    main()
