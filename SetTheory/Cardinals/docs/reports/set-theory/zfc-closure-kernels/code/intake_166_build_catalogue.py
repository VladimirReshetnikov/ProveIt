"""Build/inspect only the batch166 collection MANIFEST in new external scratch.

Adapted from batch165. Source preparation does not run this script. Three TeX
passes, PDF metadata/font checks and page rendering are separate from actual
visual review; no delivered article or proof-assistant compiler is invoked.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--catalogue-root', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--allow-preview', action='store_true')
    a = p.parse_args()
    repo = a.repo.resolve()
    catalogue = a.catalogue_root.resolve() if a.catalogue_root else repo
    work = a.output.resolve()
    if work.is_relative_to(repo) or work.exists():
        p.error('Use a new external output directory.')
    source = catalogue / 'SetTheory/Cardinals/docs/reports/manifest.tex'
    content = source.read_text()
    preview = 'WRITE166SHA' in content
    if preview and not a.allow_preview:
        p.error('Replace WRITE166SHA before final build, or explicitly allow a preview.')
    assert 'Batch~166' in content and 'Seventy manuscripts' in content
    work.mkdir(parents=True)
    shutil.copyfile(source, work / 'manifest.tex')
    sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    commands = []
    for i in range(1, 4):
        print(f'MANIFEST TeX pass {i}/3', flush=True)
        cmd = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'manifest.tex']
        result = subprocess.run(cmd, cwd=work, capture_output=True, text=True, timeout=120)
        log = work / f'pass{i}.txt'
        log.write_text(result.stdout + result.stderr)
        commands.append(dict(pass_number=i, command=cmd, returncode=result.returncode, log_sha256=sha(log)))
        assert result.returncode == 0, (work, result.stdout[-3000:])
    log = (work / 'manifest.log').read_text()
    bad = [line for line in log.splitlines() if re.search(r'(^!|LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined|multiply defined|duplicate.*destination)', line)]
    assert not bad, bad
    info = subprocess.check_output(['pdfinfo', str(work / 'manifest.pdf')], text=True, timeout=30)
    fonts = subprocess.check_output(['pdffonts', str(work / 'manifest.pdf')], text=True, timeout=30)
    text = subprocess.check_output(['pdftotext', '-layout', str(work / 'manifest.pdf'), '-'], text=True, timeout=30)
    (work / 'pdfinfo.txt').write_text(info)
    (work / 'pdffonts.txt').write_text(fonts)
    (work / 'manifest.txt').write_text(text)
    pages = int(re.search(r'Pages:\s+(\d+)', info).group(1))
    font_rows = [re.search(r'\s+(yes|no)\s+(yes|no)\s+(yes|no)\s+\d+\s+\d+\s*$', row) for row in fonts.splitlines()[2:]]
    assert font_rows and all(row is not None and row.group(1) == 'yes' for row in font_rows)
    normalized = {i: ' '.join(page.split()) for i, page in enumerate(text.split('\f'), 1) if i <= pages}
    changed = {i for i, page in normalized.items() if any(marker in page for marker in ['Batch 166', 'batch 166', 'Seventy', 'seventy'])}
    entry_starts = [i for i, page in normalized.items() if i >= 4 and 'ZFC closure kernels and small inconsistency-search machines' in page]
    assert entry_starts, 'Could not locate the actual extended host entry in extracted PDF text.'
    entry_start = min(entry_starts)
    # This host is the final catalogue entry, verified from the source layout.
    assert content.rfind(r'\entry{') == content.index(r'\entry{ZFC closure kernels and small inconsistency-search machines}')
    rendered = sorted({1, 2, *changed, *range(entry_start, pages + 1)})
    for page in rendered:
        print(f'Render MANIFEST page {page}/{pages}', flush=True)
        subprocess.run(['pdftoppm', '-f', str(page), '-singlefile', '-scale-to', '1300', '-png', str(work / 'manifest.pdf'), str(work / f'page-{page}')], check=True, capture_output=True, timeout=30)
    record = dict(status='BUILT_VISUAL_REVIEW_PENDING', batch=166,
                  scratch=str(work), source=str(source), source_sha256=sha(source),
                  built_source_sha256=sha(work / 'manifest.tex'), pdf_sha256=sha(work / 'manifest.pdf'),
                  preview_with_write_placeholder=preview, commands=commands,
                  pages=pages, font_records=len(font_rows), all_fonts_embedded=True,
                  final_warnings_or_boxes=bad, changed_pages_detected=sorted(changed),
                  complete_host_entry_first_page=entry_start, rendered_pages=rendered,
                  visual_review_pending=True, proof_compiler_calls=0,
                  scope='Scratch collection MANIFEST only; no delivered article/PDF edits or proof build. Do not publish a preview PDF or claim visual QA before actually viewing rendered pages.')
    (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
