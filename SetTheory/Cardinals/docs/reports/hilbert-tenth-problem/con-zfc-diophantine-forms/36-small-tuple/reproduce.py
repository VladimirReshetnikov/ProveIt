#!/usr/bin/env python3
"""Reconstruct the recommended instance and run the offline verification."""
from pathlib import Path
import subprocess
import sys

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    raise SystemExit(subprocess.call([sys.executable,str(root/'verify.py'),'--rebuild'],cwd=root))
