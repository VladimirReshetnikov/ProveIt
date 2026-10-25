#!/usr/bin/env python3
"""UNSEALED draft: deterministic scratch typesetting of the complemented47 page.

CODE/TEX DRAFT ONLY. Final accepted Pc3, two full statics and separate ROOT
release precede execution. No producer or native application is imported.
"""
import sys

sys.dont_write_bytecode = True

import argparse
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]
PAGE = ROOT/'candidates/one-page-compact66-complemented47'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
ARTIFACTS = ['equation.pdf', 'equation.txt', 'RENDER.txt', 'TEX_DIAGNOSTICS.txt', 'RENDER_DATA.json']


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True)+'\n').encode()


def strict_pairs(items):
    value = {}
    for key, item in items:
        need(key not in value, 'duplicate bootstrap JSON key')
        value[key] = item
    return value


def reject_constant(value):
    raise ValueError('nonfinite bootstrap JSON constant '+value)


def bootstrap_guard():
    """Authenticate the only adopted module before executing any of its code."""
    for path in [PAGE/'SOURCE_PINS.json', PAGE/'guard.py']:
        need(path.is_file() and not path.is_symlink(), 'regular bootstrap input')
        need(all(not parent.is_symlink() for parent in path.parents),
             'no bootstrap path-component symlink')
    pins = json.loads((PAGE/'SOURCE_PINS.json').read_bytes(),
                      object_pairs_hook=strict_pairs, parse_constant=reject_constant)
    need(type(pins) is dict and type(pins.get('own_core')) is dict,
         'bootstrap own-core mapping')
    name = 'candidates/one-page-compact66-complemented47/guard.py'
    pin = pins['own_core'].get(name)
    need(type(pin) is dict and set(pin) == {'bytes', 'sha256'} and
         type(pin['bytes']) is int and pin['bytes'] >= 0 and
         type(pin['sha256']) is str and re.fullmatch(r'[0-9a-f]{64}', pin['sha256']),
         'bootstrap guard byte/hash record')
    raw = (PAGE/'guard.py').read_bytes()
    need(pin == {'bytes': len(raw), 'sha256': digest(raw)}, 'whole pinned guard before import')
    spec = spec_from_file_location('compact66_complemented47_page_guard', PAGE/'guard.py')
    need(spec is not None and spec.loader is not None, 'pinned guard loader')
    guard = module_from_spec(spec)
    spec.loader.exec_module(guard)
    return guard


def normalized_log(raw, scratch):
    text = raw.decode('utf-8', errors='replace').replace(str(scratch), '<scratch>')
    # Omit only the engine's wall-clock log header, retaining other diagnostics.
    text = re.sub(r'(This is .*?)\s+\d{1,2} [A-Z]{3} \d{4} \d\d:\d\d\s*$',
                  r'\1 <clock omitted>', text, flags=re.M)
    return ('\n'.join(line.rstrip() for line in text.splitlines()).rstrip()+'\n').encode()


def build():
    tex = (PAGE/'equation.tex').read_bytes()
    text = tex.decode()
    need(r'\usepackage[letterpaper,margin=.38in]{geometry}' in text, 'reviewed Letter geometry')
    need(r'\fontsize{9}{9.5}\selectfont' in text, 'reviewed9point body')
    need(r'\fontsize{7.7}{8.2}\selectfont\ttfamily' in text, 'verbatim reviewed7.7point seed')
    need('%%SEED%%' not in text and text.count(ALPHABET) == 1, 'standalone complete literal recipe')
    seed = (PAGE/'SEED.txt').read_text().strip()
    need(len(seed) == 436 and set(seed) <= set(ALPHABET), 'whole436-character seed')
    with TemporaryDirectory(prefix='compact66-complemented47-render-') as temporary:
        work = Path(temporary)
        (work/'equation.tex').write_bytes(tex)
        env = dict(os.environ)
        env.update(SOURCE_DATE_EPOCH='946684800', FORCE_SOURCE_DATE='1', TZ='UTC',
                   openin_any='p', openout_any='p')
        run = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                              '-halt-on-error', '-file-line-error', 'equation.tex'],
                             cwd=work, env=env, capture_output=True, timeout=60)
        render = normalized_log(run.stdout+run.stderr, work)
        need(run.returncode == 0, 'pdflatex success; full scratch transcript:\n'+render.decode(errors='replace'))
        diagnostics = normalized_log((work/'equation.log').read_bytes(), work)
        need(b'Overfull' not in render and b'Overfull' not in diagnostics,
             'zero overfull boxes required; full transcript:\n'+render.decode(errors='replace'))
        pdf = (work/'equation.pdf').read_bytes()
        info = subprocess.run(['pdfinfo', 'equation.pdf'], cwd=work, env=env,
                              check=True, capture_output=True, text=True, timeout=30).stdout
        need(re.search(r'Pages:\s+1\b', info) and '612 x 792' in info,
             'exactly one Letter page; actual pdfinfo:\n'+info)
        extracted = subprocess.run(['pdftotext', '-raw', 'equation.pdf', '-'], cwd=work,
                                   env=env, check=True, capture_output=True, timeout=30).stdout
        compact = re.sub(r'\s', '', extracted.decode())
        need(seed in compact and ALPHABET in compact, 'every actual seed/alphabet character')
        need('exactdegree157;a66-operationevaluator.' in compact, 'actual printed cost/degree')
        need('J,F,α,z,f,h,i,T,s,w,τ,η,ζ,y,γ∈Z>0.' in compact, 'actual printed fifteen-positive signature')
        data = {'equation.pdf': pdf, 'equation.txt': extracted,
                'RENDER.txt': render, 'TEX_DIAGNOSTICS.txt': diagnostics}
        record = {'schema': 'compact66_complemented47_complete_page_render_data_v1', 'pages': 1, 'paper': 'Letter',
                  'scope': 'Deterministic scratch typesetting only. Actual-TeX graph/whole-tuple/PDF audit and visual review are separate requirements.',
                  'body_font_pt': 9, 'seed_font_pt': 7.7, 'no_overfull_boxes': True,
                  'all436_seed_characters_exact': True, 'all62_alphabet_characters_exact': True,
                  'nonwhite_pdf_characters': len(compact), 'tex_sha256': digest(tex),
                  'renderer_sha256': digest(Path(__file__).read_bytes()),
                  'sha256': {name: digest(blob) for name, blob in sorted(data.items())},
                  'canonical_page_unchanged': True}
        data['RENDER_DATA.json'] = encoded(record)
    return data, record


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--render', action='store_true', help='materialize fixed scratch results without changing TeX')
    mode.add_argument('--check', action='store_true', help='private pure rerender and full byte comparison')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    guard = bootstrap_guard()
    guard.authenticate(materialized=True)
    role = 'render' if args.render else 'rerender-optimized' if sys.flags.optimize else 'rerender'
    guard.receipt_path(role, args.output)
    before = guard.snapshot()
    for name in ARTIFACTS:
        path = PAGE/name
        need(not path.is_symlink(), 'no artifact symlink')
        need(path.is_file() if args.check else not path.exists(),
             'existing check artifact' if args.check else 'absent initial render artifact')
    data, record = build()
    for name in ARTIFACTS:
        path = PAGE/name
        need(not path.is_symlink(), 'no artifact symlink')
        if args.check:
            need(path.is_file() and path.read_bytes() == data[name], 'byte-exact deterministic result '+name)
        else:
            need(not path.exists(), 'initial render artifact remains absent')
    receipt = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
               'mode': 'pure rerender --check' if args.check else 'scratch render materialization',
               'all_generated_artifact_bytes_exact': True, 'render': record,
               'operations': 66, 'exact_degree': 157,
               'source_pins_sha256': digest((PAGE/'SOURCE_PINS.json').read_bytes()),
               'source_index_sha256': digest((PAGE/'SOURCE_INDEX.json').read_bytes()),
               'scope': 'The fifteen-positive P66 with one coherent complemented47 indexed943 tuple; this render does not accept source calibration or promote or modify the maintained page.',
               'artifact_hashes': {name: digest(data[name]) for name in ARTIFACTS}}
    raw = encoded(receipt)
    guard.unchanged(before)
    guard.receipt_path(role, args.output)
    if args.render:
        for name in ARTIFACTS:
            with (PAGE/name).open('xb') as target:
                target.write(data[name])
    guard.unchanged(before, allowed=ARTIFACTS if args.render else ())
    guard.receipt(role, raw, args.output)


if __name__ == '__main__':
    main()
