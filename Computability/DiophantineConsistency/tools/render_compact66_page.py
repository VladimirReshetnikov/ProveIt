#!/usr/bin/env python3
"""Held deterministic scratch typesetting of the complete compact66 page.

CODE ONLY/HOLD. Two complete static reviews and explicit release precede
execution. No project imports, source production or coefficient generation.
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
PAGE = ROOT/'candidates/one-page-compact66'
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
    pins=json.loads((PAGE/'SOURCE_PINS.json').read_bytes())
    for group in ['external_files','own_core']:
        for name,pin in pins[group].items():
            path=ROOT/name
            raw=path.read_bytes()
            need(not path.is_symlink() and {'bytes':len(raw),'sha256':digest(raw)}==pin,'whole reviewed input '+name)
    required={'candidates/one-page-fifteen66':'065a396f78fb271b1b82cadd2d61b9a79f774cd82739d41946b1a9fcf8384424',
              'research/grouped-fixed-coefficient-recipe':'f5ae707993e3041a6d35f4144e0baade3cfa45fd3d4f5875c825771fad1a9594',
              'research/indexed-tile-enumeration':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
         'research/compact-tile-parameters':'5dafe5e3d18abb8d8a4e2254d7ac777d9db21933a8b768eba2c46535a9e3fdf9',
         'research/binary-pass-cleanup-tiles':'80d44e88695ed56036aaeab3a50292a388bbf2cd7e960463125c7a75fb349a6c',
         'candidates/one-page-grouped66':'187ce13905b346ccb435e86745b60f212dc46c9c726307e5cd82cb98b9e7c886'}
    need({d['folder']:d['manifest_sha256'] for d in pins['closed_dependencies']}==required,'six whole calibrated native/source/page contracts')
    for name,seal in required.items():
        folder=ROOT/name
        raw=(folder/'MANIFEST.json').read_bytes()
        need(digest(raw)==seal,'exact inherited seal')
        files=json.loads(raw)['files']
        actual={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(actual==set(files),'complete inherited inventory')
        for relative,pin in files.items():
            path=folder/relative
            data=path.read_bytes()
            expected={'sha256':digest(data),'bytes':len(data)} if isinstance(pin,dict) else digest(data)
            need(not path.is_symlink() and pin==expected,'whole inherited member '+relative)
    index=json.loads((PAGE/'SOURCE_INDEX.json').read_bytes())
    need(set(index)=={'schema','files','producer_sha256','source_pins_sha256'} and
         index['schema']=='indexed_p66_source_inventory_v1','complete materialized source inventory schema')
    need(set(index['files'])=={'polynomial.json','COEFFICIENT_BINDING.json','CALIBRATION_BINDING.json'},'whole materialized source records')
    for name,pin in index['files'].items():
        path=PAGE/name
        raw=path.read_bytes()
        need(not path.is_symlink() and pin=={'bytes':len(raw),'sha256':digest(raw)},'complete new source record '+name)
    need(index['producer_sha256']==digest((PAGE/'build.py').read_bytes()) and index['source_pins_sha256']==digest((PAGE/'SOURCE_PINS.json').read_bytes()),'reviewed source producer and pins')
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
    with TemporaryDirectory(prefix='compact66-render-') as temporary:
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
        record = {'schema': 'compact66_complete_page_render_data_v1', 'pages': 1, 'paper': 'Letter',
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
        need(not path.is_symlink(), 'no artifact symlink')
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes() == data[name], 'byte-exact deterministic result '+name)
    receipt = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
               'mode': 'pure rerender --check' if args.check else 'scratch render materialization',
               'all_generated_artifact_bytes_exact': True, 'render': record,
               'operations': 66, 'exact_degree': 157,
               'source_pins_sha256': digest((PAGE/'SOURCE_PINS.json').read_bytes()),
               'scope': 'The accepted fifteen-positive P66 and whole indexed943 integers with a shorter equivalent fixed recipe; this render does not promote or modify the maintained page.',
               'artifact_hashes': {name: digest(data[name]) for name in ARTIFACTS}}
    raw = encoded(receipt)
    pins = json.loads((PAGE/'SOURCE_PINS.json').read_bytes())
    protected = {(ROOT/n).resolve() for group in ['external_files', 'own_core'] for n in pins[group]}
    protected |= {(PAGE/n).resolve() for n in ARTIFACTS+['SOURCE_PINS.json', 'HOLD_INVENTORY.json', 'MANIFEST.json',
                                                       'polynomial.json', 'COEFFICIENT_BINDING.json', 'CALIBRATION_BINDING.json', 'SOURCE_INDEX.json']}
    need(args.output.resolve()!=ROOT.parents[1].resolve() and ROOT.parents[1].resolve() not in args.output.resolve().parents,
         'receipt must remain outside the repository')
    need(not args.output.is_symlink() and args.output.resolve() not in protected, 'separate render receipt')
    if args.output.exists():
        need(args.output.read_bytes() == raw, 'refuse changed existing render receipt')
    if not args.check:
        for name in ARTIFACTS:
            if not (PAGE/name).exists():
                (PAGE/name).write_bytes(data[name])
    args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
