"""Compatibility entry point for the reproducible two-engine benchmark."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1]/'tools'/'benchmark.py'),run_name='__main__')
