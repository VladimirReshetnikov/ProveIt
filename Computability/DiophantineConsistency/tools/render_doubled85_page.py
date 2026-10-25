#!/usr/bin/env python3
"""Held deterministic scratch typesetting of the complete doubled85 page.

CODE ONLY/HOLD. Two complete static reviews and explicit release precede
execution. No project imports, graph producer or coefficient generation.
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
PAGE = ROOT/'candidates/one-page-doubled85'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
ARTIFACTS = ['equation.pdf', 'equation.txt', 'RENDER.txt', 'TEX_DIAGNOSTICS.txt', 'RENDER_DATA.json']


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True)+'\n').encode()


def authenticate():
    pins = json.loads((PAGE/'SOURCE_PINS.json').read_bytes())
    for group in ['external_files', 'own_core']:
        for name, pin in pins[group].items():
            data = (ROOT/name).read_bytes()
            need(digest(data) == pin['sha256'] and len(data) == pin['bytes'], 'whole reviewed '+group+' '+name)
    required = {'candidates/one-page-saturated10', 'research/indexed-tile-enumeration',
                'research/ten-positive-doubled-product-square'}
    need({dep['folder'] for dep in pins['closed_dependencies']} == required, 'three complete calibrated parents')
    for dep in pins['closed_dependencies']:
        folder = ROOT/dep['folder']
        raw = (folder/'MANIFEST.json').read_bytes()
        need(digest(raw) == dep['manifest_sha256'], 'exact inherited seal')
        files = json.loads(raw)['files']
        actual = {str(p.relative_to(folder)) for p in folder.rglob('*')
                  if p.is_file() and p != folder/'MANIFEST.json'}
        need(actual == set(files), 'complete inherited inventory')
        for name, pin in files.items():
            data = (folder/name).read_bytes()
            expected = {'sha256': digest(data), 'bytes': len(data)} if isinstance(pin, dict) else digest(data)
            need(pin == expected, 'whole inherited member '+name)
    need(pins['ordinary_completeness_premise'] == 'canonical R>3q>=96', 'explicit repaired ordinary scope')
    return pins


def normalized_log(raw, scratch):
    text = raw.decode('utf-8', errors='replace').replace(str(scratch), '<scratch>')
    # Omit only the engine's wall-clock log header, retaining other diagnostics.
    text = re.sub(r'(This is .*?)\s+\d{1,2} [A-Z]{3} \d{4} \d\d:\d\d\s*$',
                  r'\1 <clock omitted>', text, flags=re.M)
    return ('\n'.join(line.rstrip() for line in text.splitlines()).rstrip()+'\n').encode()


def build():
    authenticate()
    tex = (PAGE/'equation.tex').read_bytes()
    text = tex.decode()
    need(r'\usepackage[letterpaper,margin=.38in]{geometry}' in text, 'reviewed Letter geometry')
    need(r'\fontsize{9}{9.5}\selectfont' in text, 'reviewed9point body')
    need(r'\fontsize{7.7}{8.2}\selectfont\ttfamily' in text, 'verbatim reviewed7.7point seed')
    need('%%SEED%%' not in text and text.count(ALPHABET) == 1, 'standalone complete literal recipe')
    seed = (PAGE/'SEED.txt').read_text().strip()
    need(len(seed) == 436 and set(seed) <= set(ALPHABET), 'whole436-character seed')
    with TemporaryDirectory(prefix='doubled85-render-') as temporary:
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
        need('exactdegree328;an85-operationevaluator.' in compact, 'actual printed cost/degree')
        need('J,F,α,i,T,w,Y,n,η,ζ∈Z>0.' in compact, 'actual printed ten-positive signature')
        data = {'equation.pdf': pdf, 'equation.txt': extracted,
                'RENDER.txt': render, 'TEX_DIAGNOSTICS.txt': diagnostics}
        record = {'schema': 'doubled85_complete_page_render_data_v1', 'pages': 1, 'paper': 'Letter',
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
    data, record = build()
    for name in ARTIFACTS:
        path = PAGE/name
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes() == data[name], 'byte-exact deterministic result '+name)
        else:
            path.write_bytes(data[name])
    receipt = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
               'mode': 'pure rerender --check' if args.check else 'scratch render materialization',
               'all_generated_artifact_bytes_exact': True, 'render': record,
               'operations': 85, 'exact_degree': 328,
               'source_pins_sha256': digest((PAGE/'SOURCE_PINS.json').read_bytes()),
               'scope': 'Lower evaluator cost and higher degree than canonical92/283; this render does not promote the canonical page.',
               'artifact_hashes': {name: digest(data[name]) for name in ARTIFACTS}}
    raw = encoded(receipt)
    if args.output.exists():
        need(args.output.read_bytes() == raw, 'refuse changed existing render receipt')
    else:
        args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
