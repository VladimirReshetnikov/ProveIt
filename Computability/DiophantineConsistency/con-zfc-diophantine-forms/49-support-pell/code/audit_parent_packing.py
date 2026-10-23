#!/usr/bin/env python3
"""Current support-aware parent/extraction audit.

The original full-Sidon package-40 auditor is preserved only under
upstream/audit_parent_packing_PACKAGE40.py. This dispatcher runs the
current exact symbolic checker, including inactive-pair collisions.
"""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1] / 'verify.py'), run_name='__main__')
