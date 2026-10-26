#!/usr/bin/env python3
"""Evaluate one explicitly supplied integer tuple; see --help."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent / "algebra/evaluate.py"), run_name="__main__")
