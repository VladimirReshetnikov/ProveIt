#!/usr/bin/env python3
"""Compatibility entry point for the current support-aware finite auditor.

The original package-45 verifier is preserved under upstream/ and is not
applicable to the new non-Sidon labels. All checks here remain active under -O.
"""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1] / 'verify.py'), run_name='__main__')
