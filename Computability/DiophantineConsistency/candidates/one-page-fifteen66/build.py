#!/usr/bin/env python3
"""Held literal whole-indexed P66 metadata specialization, without arithmetic changes."""
import argparse
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLD = 'fixed/source54-p66.json'
PRESERVED = ROOT/'candidates/one-page-doubled85'
INDEXED = ROOT/'research/indexed-tile-enumeration'
OUTPUTS = ['polynomial.json', 'COEFFICIENT_BINDING.json', 'CALIBRATION_BINDING.json', 'SOURCE_INDEX.json']
SEALS = {'candidates/one-page-doubled85':'606d77c216f6464447f0682d4d0d26a35d5ddcbcc6f4d519929ad8871797ad48',
         'research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
         'research/ten-positive-index-weight':'cf3825ce1852236545c09bcf54e30ade41c8e79d3a5e9ace6ac61b08580d5d54'}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()


def read(path):
    return json.loads(path.read_bytes())


def authenticate():
    pins = read(HERE/'SOURCE_PINS.json')
    for group in ['external_files', 'own_core']:
        for name, pin in pins[group].items():
            path = ROOT/name
            raw = path.read_bytes()
            need(not path.is_symlink() and {'bytes':len(raw),'sha256':digest(raw)} == pin, 'whole reviewed input '+name)
    need({d['folder']:d['manifest_sha256'] for d in pins['closed_dependencies']} == SEALS, 'three whole source/native/page contracts')
    for name, seal in SEALS.items():
        folder = ROOT/name
        raw = (folder/'MANIFEST.json').read_bytes()
        need(digest(raw) == seal, 'exact whole parent seal')
        entries = json.loads(raw)['files']
        actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(actual == set(entries), 'complete parent inventory')
        for relative, entry in entries.items():
            path = folder/relative
            data = path.read_bytes()
            expected = {'bytes':len(data),'sha256':digest(data)} if isinstance(entry,dict) else digest(data)
            need(not path.is_symlink() and entry == expected, 'whole parent member '+relative)
    return pins


def prepare(pins):
    old = read(HERE/OLD)
    parent = read(PRESERVED/'polynomial.json')
    ports = deepcopy(parent['coefficient_binding']['ports'])
    total = 0
    for name, pin in ports.items():
        blob = (HERE/'coefficients'/pin['file']).read_bytes()
        need(blob == (PRESERVED/'coefficients'/pin['file']).read_bytes() ==
             (INDEXED/'coefficients'/pin['file']).read_bytes(), 'complete three-way indexed port '+name)
        raw = gzip.decompress(blob)
        value = int.from_bytes(raw,'little')
        need(digest(blob)==pin['gzip_sha256'] and digest(raw)==pin['raw_sha256'] and
             value.bit_length()==pin['bits'] and raw==value.to_bytes((pin['bits']+7)//8,'little'), 'canonical entire indexed integer '+name)
        total += len(raw)
    need(total == 295388, 'whole four-port raw byte census')
    binding = {'schema':'whole_indexed_p66_binding_v1','path':'coefficients/','ports':ports,'raw_bytes':total,
               'tuple':'whole directly indexed BFS943; new P66 specialization; MF_source shifted once',
               'ordinary_proof':'PROOF.md','indexed_seal':SEALS['research/indexed-tile-enumeration']}
    packet = deepcopy(old)
    packet.update(name='indexed_p66_degree157', coefficient_binding=binding, proof='PROOF.md',
                  proof_boundary='Whole indexed normalized-positive source and canonical R=3 mod4 composed with source54 section8; ordinary inherited calibration, no new formal-kernel certificate.')
    calibration = {'schema':'whole_indexed_p66_calibration_v1','historical_free_port_source':OLD,
                   'historical_sha256':digest((HERE/OLD).read_bytes()),'all_arithmetic_rows_unchanged':True,
                   'old_and_new_specialized_polynomials_identified':False,'all_four_ports_bound_together':True,
                   'source_interface':'whole indexed normalized positive native source; fresh canonical R=3 mod4',
                   'soundness_map':'T_old=f*T; retain every other positive input and all current indexed ports',
                   'completeness_map':'fresh V=chi_S(R)/S,y=psi_S(R),T=(V+c+R*f^2)/(c*f^2)',
                   'fresh_native_and_rank_witnesses':True,'closed_dependencies':SEALS,
                   'proof_sha256':digest((HERE/'PROOF.md').read_bytes()),'raw_port_bytes':total,
                   'scope':'Ordinary composed calibration; finite programs check literal binding, not the unbounded compiler proof or consistency.'}
    data = {name:encoded(value) for name,value in [('polynomial.json',packet),('COEFFICIENT_BINDING.json',binding),('CALIBRATION_BINDING.json',calibration)]}
    index = {'schema':'indexed_p66_source_inventory_v1','files':{n:{'bytes':len(b),'sha256':digest(b)} for n,b in data.items()},
             'producer_sha256':digest(Path(__file__).read_bytes()),'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes())}
    data['SOURCE_INDEX.json'] = encoded(index)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = authenticate()
    data = prepare(pins)
    for name in OUTPUTS:
        path = HERE/name
        need(not path.is_symlink(), 'no generated symlink')
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes()==data[name], 'complete deterministic source '+name)
    report = {'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'pure source check' if args.check else 'literal source materialization',
              'operations':66,'exact_degree':157,'all66_arithmetic_rows_unchanged':True,'whole_indexed_port_bytes':295388,
              'files':{n:{'bytes':len(b),'sha256':digest(b)} for n,b in data.items()},
              'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes()),'producer_sha256':digest(Path(__file__).read_bytes()),
              'scope':'New whole indexed P66 metadata; no arithmetic rewrite, TeX/PDF build, source compiler or consistency test.'}
    raw = encoded(report)
    protected = {(ROOT/n).resolve() for group in ['external_files','own_core'] for n in pins[group]}
    protected |= {(HERE/n).resolve() for n in OUTPUTS+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json','equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']}
    output = args.output.resolve()
    need(not args.output.is_symlink() and output not in protected and
         (not args.output.exists() or args.output.read_bytes()==raw), 'separate fresh or identical receipt')
    if not args.check:
        for name, blob in data.items():
            if not (HERE/name).exists():
                (HERE/name).write_bytes(blob)
    args.output.write_bytes(raw)
    print(raw.decode(),end='')


if __name__ == '__main__':
    main()
