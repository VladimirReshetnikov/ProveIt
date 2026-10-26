#!/usr/bin/env python3
"""Rebuild every new quartic coefficient stage from the frozen parent.

Uses the supplied producer programs. Independent verification is in verify.py.
Requires an empty destination and never changes the retained release files.
"""
from pathlib import Path
import argparse
import contextlib
import hashlib
import io
import json
import shutil

import build_growth
import compose_radix
import build_affine_radix
import transfer_optimizations

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rebuild(destination):
    destination = destination.resolve()
    require(not destination.exists() or not any(destination.iterdir()),
            'Rebuild destination must be empty: '+str(destination))
    destination.mkdir(parents=True, exist_ok=True)
    mappings = []
    with contextlib.redirect_stdout(io.StringIO()):
        build_growth.build(ROOT/'inherited/anchor/source/anchor219/equation.json',
                           destination/'stages/growth217')
        compose_radix.build(destination/'stages/growth217/equation.json',
                            destination/'work/main')
        for source, target in [('source216','source216'),
                               ('projection211','projection211'),
                               ('projection210_r0_v33','projection210')]:
            shutil.copytree(destination/'work/main'/source, destination/'stages'/target)
        transfer_optimizations.build(destination/'stages/projection210/equation.json',
                                     destination/'equations/principal210', profile_index=1)
        build_affine_radix.build('anchor221', destination/'work/balanced')
        for source, target in [('source','balanced_source220'),
                               ('radical','balanced_projection215'),
                               ('affine_r0_v33','balanced_projection214')]:
            shutil.copytree(destination/'work/balanced'/source, destination/'stages'/target)
        transfer_optimizations.build(destination/'stages/balanced_projection214/equation.json',
                                     destination/'equations/balanced214', profile_index=0)
    for relative in [
            'stages/growth217','stages/source216','stages/projection211','stages/projection210',
            'stages/balanced_source220','stages/balanced_projection215','stages/balanced_projection214',
            'equations/principal210','equations/balanced214']:
        files = []
        for retained in sorted((ROOT/relative).glob('*.json')):
            generated = destination/relative/retained.name
            require(generated.is_file(), 'Rebuild file missing: '+relative+'/'+retained.name)
            raw = generated.read_bytes()
            require(raw == retained.read_bytes(), 'Rebuild differs: '+relative+'/'+retained.name)
            files.append({'file':retained.name,'sha256':hashlib.sha256(raw).hexdigest()})
        mappings.append({'stage':relative, 'byte_identical_files':files})
    # This directory was created above inside an initially empty destination.
    # It contains only alternative generated projection charts, not user data.
    shutil.rmtree(destination/'work')
    return {'status':'PASS','stages':mappings,
            'files_byte_identical':sum(len(stage['byte_identical_files']) for stage in mappings),
            'scope':'Exact coefficient reconstruction from the frozen parent; semantic changes require the report proofs.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    receipt = rebuild(args.output_dir)
    rendered = json.dumps(receipt, indent=2)+'\n'
    if args.receipt:
        args.receipt.write_text(rendered)
    print(rendered, end='')
