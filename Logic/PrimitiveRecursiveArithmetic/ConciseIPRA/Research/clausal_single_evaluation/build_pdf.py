"""Build the standalone report with an installed, configured TeX Live."""
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parent
    command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex']
    for _ in range(3):
        subprocess.run(command, cwd=root, check=True)
    print(root / 'report.pdf')


if __name__ == '__main__':
    main()
