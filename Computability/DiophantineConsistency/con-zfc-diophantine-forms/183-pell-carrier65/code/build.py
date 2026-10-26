#!/usr/bin/env python3
"""Reconstruct all three literal equations and all four fixed integers."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys
from arithmetic import make_child
from coefficients import new_decode, tiles, constants
from domain_translations import translate

ROOT = Path(__file__).resolve().parents[1]

def canonical(obj):
    return (json.dumps(obj, indent=2, sort_keys=True)+'\n').encode()

def construct():
    parent = json.loads((ROOT/'sources/parent_polynomial.json').read_text())
    graph = make_child(parent)
    seed = (ROOT/'equation/SEED.txt').read_text().strip()
    ports = constants(tiles(new_decode(seed)))
    files = {
        'carrier65.json': canonical(graph),
        'natural14.json': canonical(translate(graph, 'natural')),
        'integer42.json': canonical(translate(graph, 'integer')),
    }
    manifest = {}
    for name, value in ports.items():
        raw = value.to_bytes((value.bit_length()+7)//8, 'big')
        files['coefficients/'+name+'.bin'] = raw
        manifest[name] = dict(bits=value.bit_length(), bytes=len(raw),
            encoding='minimal unsigned big-endian',
            sha256=hashlib.sha256(raw).hexdigest())
    files['coefficients.json'] = canonical(manifest)
    return files

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
        help='New directory for independently reconstructed equation files')
    args = parser.parse_args()
    files = construct()
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=False)
        for relative, raw in files.items():
            path = args.output_dir/relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        print(json.dumps({'status':'PASS','files_written':len(files)}, sort_keys=True))
    else:
        for relative, raw in files.items():
            if (ROOT/'equation'/relative).read_bytes() != raw:
                raise ValueError('Reconstruction mismatch: '+relative)
        print(json.dumps({'status':'PASS','byte_identical_files':len(files)},sort_keys=True))

if __name__ == '__main__':
    main()
