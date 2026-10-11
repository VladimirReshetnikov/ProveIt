#!/usr/bin/env python3
"""Compile the self-contained article without retaining temporary TeX debris."""
from __future__ import annotations
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def write_index(aux: str) -> None:
    """Extract only stable labels/numbers/pages, not TeX's transient AUX file."""
    pattern=re.compile(r'^\\newlabel\{(tlbc:[^}]*)\}\{\{([^}]*)\}\{([^}]*)\}',re.MULTILINE)
    entries=[]
    kinds={'thm':'Theorem','cor':'Corollary','lem':'Lemma','prop':'Proposition',
           'def':'Definition','ex':'Example','eq':'Equation','sec':'Section'}
    for label,number,page in pattern.findall(aux):
        if '@' in label:continue
        part=label.split(':')[1]
        entries.append({'label':label,'number':number,'page':int(page) if page.isdigit() else page,
                        'kind':kinds.get(part,part)})
    target=ROOT/'integration';target.mkdir(exist_ok=True)
    (target/'theorem_index.json').write_text(json.dumps(entries,indent=2)+'\n')
    rows=['# Theorem and proposition index','',
          'Generated from the delivered standalone LaTeX build. Rebuilding regenerates this index.',
          '', '| Result | Page | Label |','|---|---:|---|']
    for e in entries:
        if e['kind'] not in ('Equation','Section'):
            rows.append(f"| {e['kind']} {e['number']} | {e['page']} | `{e['label']}` |")
    (target/'theorem_index.md').write_text('\n'.join(rows)+'\n')

def main() -> None:
    engine=shutil.which('pdflatex')
    if engine is None:
        raise SystemExit('pdflatex is required; install a standard TeX distribution.')
    with tempfile.TemporaryDirectory(prefix='tlbc-build-') as temp:
        work=Path(temp)
        shutil.copy2(ROOT/'article.tex',work/'article.tex')
        logs=[]
        for run in range(3):
            result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','article.tex'],
                                  cwd=work,text=True,capture_output=True)
            logs.append(result.stdout+'\n'+result.stderr)
            if result.returncode:
                (ROOT/'data'/'failed_build.log').write_text('\n'.join(logs))
                raise SystemExit('TeX build failed; see data/failed_build.log')
        text=(work/'article.log').read_text(errors='replace')
        issues=[line for line in text.splitlines() if any(t in line for t in
                ('Overfull','undefined','multiply defined','LaTeX Warning'))]
        shutil.copy2(work/'article.pdf',ROOT/'article.pdf')
        write_index((work/'article.aux').read_text())
        (ROOT/'data'/'build_receipt.json').write_text(json.dumps({
            'engine':subprocess.check_output([engine,'--version'],text=True).splitlines()[0],
            'passes':3,'status':'compiled','log_flags':issues},indent=2)+'\n')
        # Keep a complete log for the mathematical maintainer's inspection.
        (ROOT/'data'/'build.log').write_text(text)
    print('Built article.pdf')
    print(json.dumps(issues,indent=2))

if __name__=='__main__':main()
