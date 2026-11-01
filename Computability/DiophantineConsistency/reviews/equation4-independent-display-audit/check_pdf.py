#!/usr/bin/env python3
"""Independently rebuild the displayed PDF without touching the workspace."""
from pathlib import Path
import hashlib,json,subprocess,tempfile
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency';source=P/'equation4.tex';pdf=P/'equation4.pdf'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source_before=H(source);pdf_before=H(pdf)
with tempfile.TemporaryDirectory(prefix='equation4-independent-pdf-') as tmp:
 cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+tmp,str(source)]
 run=subprocess.run(cmd,cwd=R,capture_output=True,text=True);assert run.returncode==0,run.stdout+run.stderr
 built=Path(tmp)/'equation4.pdf';log=(Path(tmp)/'equation4.log').read_text();assert H(built)==pdf_before and H(source)==source_before and H(pdf)==pdf_before
 assert 'Overfull \\hbox' not in log and 'Overfull \\vbox' not in log
 print(json.dumps({'status':'PASS_INDEPENDENT_PDF_REBUILD','source_sha256':source_before,'pdf_sha256':pdf_before,'script_sha256':H(__file__),'pdflatex_exit_code':run.returncode,'font_warning_lines':sum('LaTeX Font Warning:' in l for l in log.splitlines()),'overfull_boxes':0,'scope':'Byte-identical local PDF rebuild; TeX-source semantics and source-proof ancestry are checked separately.'},indent=2,sort_keys=True))
