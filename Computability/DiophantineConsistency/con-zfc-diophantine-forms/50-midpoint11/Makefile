.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 verify.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	python3 -c "from pathlib import Path; import shutil; root=Path('.'); [p.unlink() for p in root.glob('report.*') if p.suffix in {'.aux','.log','.out','.toc'}]; [shutil.rmtree(p) for p in list(root.rglob('__pycache__'))]"
