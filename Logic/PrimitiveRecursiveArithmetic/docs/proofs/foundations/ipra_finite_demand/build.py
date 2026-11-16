#!/usr/bin/env python3
"""Reproduce the delivered PDF, exact checks, and optional Lean compilation."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
VALIDATION = ROOT / 'validation'
MODULES = ['BackwardDemand', 'FiniteHausdorff', 'AggregateTargets',
           'RootSetTargets', 'NormTargets']


def run(cmd, cwd=ROOT, env=None):
    p = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {"command": cmd, "exit_code": p.returncode, "output": p.stdout}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', default=os.environ.get('LEAN_BIN') or shutil.which('lean'))
    ap.add_argument('--skip-lean', action='store_true')
    ap.add_argument('--skip-pdf', action='store_true')
    args = ap.parse_args()
    VALIDATION.mkdir(exist_ok=True)
    summary = {"scope": "Finite implementation and compiler checks, not full embedded iPRA proofs"}

    references = {}
    for stem in ['finite_demands', 'root_sets', 'superelliptic_norm']:
        result = run([sys.executable, str(ROOT / 'code' / (stem + '.py'))])
        if result['exit_code']:
            print(result['output'])
            raise SystemExit(result['exit_code'])
        references[stem] = json.loads(result['output'])
        (VALIDATION / (stem + '_checks.json')).write_text(
            json.dumps(references[stem], indent=2) + '\n')
    summary['reference_programs'] = references

    if not args.skip_lean:
        if not args.lean:
            raise SystemExit('Lean unavailable: supply --lean /absolute/path/lean or --skip-lean')
        args.lean = str(Path(args.lean).resolve())
        outdir = ROOT / '.build' / 'lean'
        outdir.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ)
        env['LEAN_PATH'] = str(outdir)
        lean_results = {"compiler": run([args.lean, '--version'])['output'].strip(),
                        "modules": []}
        for name in MODULES:
            source = ROOT / 'lean' / (name + '.lean')
            result = run([args.lean, '-o', str(outdir / (name + '.olean')),
                          name + '.lean'], cwd=ROOT / 'lean', env=env)
            result['source'] = 'lean/' + name + '.lean'
            result['sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
            result['status'] = ('proved native lemmas' if name in MODULES[:2]
                                else 'definitions and UNPROVED named proposition targets')
            lean_results['modules'].append(result)
            if result['exit_code']:
                print(result['output'])
                (VALIDATION / 'lean_build.json').write_text(json.dumps(lean_results, indent=2) + '\n')
                raise SystemExit(result['exit_code'])
        (VALIDATION / 'lean_build.json').write_text(json.dumps(lean_results, indent=2) + '\n')
        summary['lean'] = {"compiler": lean_results['compiler'], "compiled_modules": len(MODULES),
                           "embedded_main_derivations": "not implemented"}

    if not args.skip_pdf:
        texenv = dict(os.environ)
        probe = run(['kpsewhich', 'pdflatex.fmt'])
        if probe['exit_code'] and Path('/usr/share/texlive/texmf-dist').is_dir():
            # A private fallback for minimal Debian images without generated
            # TeX databases/formats. It never changes the system installation.
            texruntime = ROOT / '.build' / 'tex-runtime'
            texruntime.mkdir(parents=True, exist_ok=True)
            texenv.update(TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}',
                          TEXFORMATS=str(texruntime) + '//:',
                          TEXFONTMAPS=str(texruntime) + '//:')
            if not (texruntime / 'pdflatex.fmt').exists():
                fmt = run(['pdftex', '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
                           '-interaction=nonstopmode', '-halt-on-error', '-no-shell-escape',
                           'pdflatex.ini'], cwd=texruntime, env=texenv)
                (VALIDATION / 'tex_format_build.txt').write_text(fmt['output'])
                if fmt['exit_code']:
                    print(fmt['output'][-6000:])
                    raise SystemExit(fmt['exit_code'])
            maps = ['/usr/share/texmf/fonts/map/dvips/lm/lm.map']
            maps += ['/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/' + n + '.map'
                     for n in ['cm', 'cmextra', 'symbols', 'latxfont']]
            (texruntime / 'pdftex.map').write_text('\n'.join(Path(p).read_text() for p in maps))
        result = run(['latexmk', '-g', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                      '-outdir=.build/tex', 'ipra_finite_demand.tex'], env=texenv)
        (VALIDATION / 'pdf_build.txt').write_text(result['output'])
        if result['exit_code']:
            print(result['output'][-8000:])
            raise SystemExit(result['exit_code'])
        output_pdf = ROOT / '.build' / 'tex' / 'ipra_finite_demand.pdf'
        shutil.copy2(output_pdf, ROOT / 'ipra_finite_demand.pdf')
        log = (ROOT / '.build' / 'tex' / 'ipra_finite_demand.log').read_text()
        warnings = [line for line in log.splitlines()
                    if re.search(r'Overfull|undefined|Missing character', line)]
        summary['pdf'] = {"built": True, "warnings": warnings,
                          "visual_review": "required separately after final build"}
    (VALIDATION / 'build_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({"status": "passed", "programs": list(references),
                      "lean_compiled": not args.skip_lean,
                      "pdf_built": not args.skip_pdf}, indent=2))


if __name__ == '__main__':
    main()
