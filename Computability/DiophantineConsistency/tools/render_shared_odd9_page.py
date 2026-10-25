#!/usr/bin/env python3
"""Deterministically typeset the complete shared-odd nine-positive comparison in scratch.

CODE PREPARATION HOLD. Do not import or execute before two complete static
reviews and an explicit root release. This renderer imports no project code
and does not emit/change the accepted graph or the held mathematical TeX.
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
PAGE = ROOT/'candidates/one-page-shared-odd9'
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
    pins = json.loads((PAGE/'TOOL_PINS.json').read_bytes())
    for key in ['external_files', 'preparation_files', 'tool_core']:
        for name, pin in pins[key].items():
            p = ROOT/name if key == 'external_files' else PAGE/name
            data = p.read_bytes()
            need(digest(data) == pin['sha256'] and len(data) == pin['bytes'], 'whole reviewed '+key+' '+name)
    prep = json.loads((PAGE/'SOURCE_PINS.json').read_bytes())
    for name, pin in prep['external_files'].items():
        data = (ROOT/name).read_bytes()
        need(digest(data) == pin['sha256'] and len(data) == pin['bytes'], 'whole preparation dependency '+name)
    for name, pin in prep['own_core'].items():
        data = (PAGE/name).read_bytes()
        need(digest(data) == pin['sha256'] and len(data) == pin['bytes'], 'whole frozen preparation member '+name)
    return pins


def normalized_log(raw, scratch):
    text = raw.decode('utf-8', errors='replace').replace(str(scratch), '<scratch>')
    # The TeX engine log header contains wall-clock diagnostics unrelated to
    # the printed document. All remaining diagnostics are retained.
    text = re.sub(r'(This is .*?)\s+\d{1,2} [A-Z]{3} \d{4} \d\d:\d\d\s*$', r'\1 <clock omitted>', text, flags=re.M)
    return ('\n'.join(line.rstrip() for line in text.splitlines()).rstrip()+'\n').encode()


def build():
    authenticate()
    tex = (PAGE/'equation.tex').read_bytes()
    text = tex.decode()
    need(r'\usepackage[letterpaper,margin=.38in]{geometry}' in text, 'reviewed Letter geometry')
    need(r'\fontsize{9}{9.0}\selectfont' in text, 'reviewed9point body')
    need(r'\fontsize{8}{8.8}\selectfont\ttfamily' in text, 'reviewed8point seed')
    need('%%SEED%%' not in text and text.count(ALPHABET) == 1, 'standalone literal constants, no seed slot')
    seed_text = (ROOT/'candidates/one-page-compression/original-base62-collected/SEED.txt').read_text().strip()
    need(len(seed_text) == 722, 'whole original seed input')
    with TemporaryDirectory(prefix='shared-odd9-render-') as tmp:
        work = Path(tmp)
        (work/'equation.tex').write_bytes(tex)
        env = dict(os.environ)
        env.update(SOURCE_DATE_EPOCH='946684800', FORCE_SOURCE_DATE='1', TZ='UTC',
                   openin_any='p', openout_any='p')
        run = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                              '-halt-on-error', '-file-line-error', 'equation.tex'],
                             cwd=work, env=env, capture_output=True, timeout=60)
        render = normalized_log(run.stdout+run.stderr, work)
        need(run.returncode == 0, 'pdflatex success; scratch transcript: '+render.decode(errors='replace'))
        diagnostics = normalized_log((work/'equation.log').read_bytes(), work)
        need(b'Overfull' not in render and b'Overfull' not in diagnostics,
             'zero overfull boxes; layout review required. Full transcript:\n'+render.decode(errors='replace'))
        pdf = (work/'equation.pdf').read_bytes()
        info_run = subprocess.run(['pdfinfo', 'equation.pdf'], cwd=work, env=env,
                                  check=True, capture_output=True, text=True, timeout=30)
        info = info_run.stdout
        need(re.search(r'Pages:\s+1\b', info) and '612 x 792' in info,
             'exactly one Letter page; fit is not assumed. Actual pdfinfo:\n'+info)
        extracted = subprocess.run(['pdftotext', '-raw', 'equation.pdf', '-'], cwd=work,
                                   env=env, check=True, capture_output=True, timeout=30).stdout
        raw_text = extracted.decode()
        compact = re.sub(r'\s', '', raw_text)
        need(seed_text in compact and ALPHABET in compact, 'every actual printed seed/alphabet character')
        need('413operations,degree1,316,546.' in compact, 'printed full evaluator cost/degree tradeoff')
        need('b,g,h,s,w,C,i,j,n∈Z>0' in compact, 'actual printed nine-positive signature')
        data = {'equation.pdf': pdf, 'equation.txt': extracted,
                'RENDER.txt': render, 'TEX_DIAGNOSTICS.txt': diagnostics}
        record = {'schema': 'shared_odd_nine_complete_page_render_data_v1',
                  'scope': 'Deterministic scratch typesetting only; independent exact actual-TeX graph/tuple audit is a separate program, and visual review is still required.',
                  'pages': 1, 'paper': 'Letter', 'body_font_pt': 9, 'seed_font_pt': 8,
                  'no_overfull_boxes': True, 'all722_seed_characters_exact': True,
                  'all62_alphabet_characters_exact': True,
                  'nonwhite_pdf_characters': len(compact), 'tex_sha256': digest(tex),
                  'renderer_sha256': digest(Path(__file__).read_bytes()),
                  'sha256': {n: digest(blob) for n, blob in sorted(data.items())},
                  'canonical_page_unchanged': True}
        data['RENDER_DATA.json'] = encoded(record)
    return data, record


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--render', action='store_true', help='materialize reviewed scratch results without changing equation.tex')
    mode.add_argument('--check', action='store_true', help='rebuild all results in private scratch and compare complete existing bytes')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    data, record = build()
    for name in ARTIFACTS:
        path = PAGE/name
        if args.check or path.exists():
            need(path.is_file() and path.read_bytes() == data[name], 'byte-exact deterministic rebuild '+name)
        else:
            path.write_bytes(data[name])
    receipt = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
               'mode': 'pure rebuild --check' if args.check else 'scratch render materialization',
               'all_generated_artifact_bytes_exact': True,
               'render': record, 'operations': 413, 'exact_degree': 1316546,
               'comparison_scope': 'Nine positive inputs with substantially larger evaluator cost/degree than canonical92/283. This comparison does not promote a canonical page.',
               'tool_pins_sha256': digest((PAGE/'TOOL_PINS.json').read_bytes()),
               'artifact_hashes': {n: digest(data[n]) for n in ARTIFACTS}}
    raw = encoded(receipt)
    if args.output.exists():
        need(args.output.read_bytes() == raw, 'refuse changed existing render/rebuild receipt')
    else:
        args.output.write_bytes(raw)
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
