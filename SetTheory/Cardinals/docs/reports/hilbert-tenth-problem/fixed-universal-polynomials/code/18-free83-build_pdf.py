#!/usr/bin/env python3
"""Build the report offline in an empty external directory, without shell escape."""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
def need(ok, message):
    if not ok: raise RuntimeError(message)
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check-packaged', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    need(out != ROOT and ROOT not in out.parents, 'Use an external build directory')
    need(not out.exists() or not any(out.iterdir()), 'Build directory must be empty')
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT/'report43.tex', out/'report43.tex')
    cache = out/'tex-cache'; cache.mkdir()
    env = dict(os.environ, TEXMF='{'+ '/usr/share/texlive/texmf-dist,/usr/share/texmf' +'}',
               TEXMFVAR=str(cache), TEXMFCONFIG=str(cache), TEXFORMATS=str(cache)+':',
               TZ='UTC', SOURCE_DATE_EPOCH='1791072000', FORCE_SOURCE_DATE='1')
    def run(argv, cwd, log):
        with log.open('wb') as stream:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=300)
        need(result.returncode == 0, 'Build failed; inspect '+str(log))
    def kpse(name):
        result = subprocess.run(['kpsewhich', name], env=env, capture_output=True, text=True)
        return result.stdout.strip() if result.returncode == 0 else ''
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
         '-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],
        cache, cache/'format.log')
    maps = []
    for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
        path = kpse(name); need(path, 'Font map unavailable: '+name)
        maps.append(Path(path).read_bytes())
    (cache/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    env['TEXFONTMAPS'] = str(cache)+':'
    for n in range(3):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
             '-halt-on-error','report43.tex'], out, out/('compile-%d.log'%(n+1)))
    raw = (out/'report43.pdf').read_bytes()
    if args.check_packaged:
        need(raw == (ROOT/'Research_Report43.pdf').read_bytes(), 'PDF bytes differ')
    print(json.dumps({'status':'PASS','bytes':len(raw),
                      'sha256':hashlib.sha256(raw).hexdigest(),
                      'source_date_epoch':1791072000,'shell_escape':False,
                      'tex_engine':subprocess.run(['pdftex','--version'],capture_output=True,text=True).stdout.splitlines()[0]},
                     sort_keys=True,indent=2))
if __name__ == '__main__': main()
