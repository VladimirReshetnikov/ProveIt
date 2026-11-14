#!/usr/bin/env python3
"""Reproduce the incremental 34-archive census without network access.

The inherited 32-archive census is not rerun. The exact commit-delta certificate
and incoming metadata bind its unchanged inputs; both added archives are freshly
parsed and classified. See the report for recognition scope and proof status.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
out = Path(tempfile.mkdtemp(prefix='pa194c-census-'))
cmd = [sys.executable, '-B', str(ROOT/'comparison/incremental_census.py'),
       '--base-census', str(ROOT/'reference/pa194/comparison/census.json'),
       '--commit-comparison', str(ROOT/'comparison/commit_range_comparison.json'),
       '--listing', str(ROOT/'comparison/current_incoming_listing.json'),
       '--new-archive', str(ROOT/'reference/archives/pa194_conpa_2026-11-13.zip'),
       '--new-archive', str(ROOT/'reference/archives/pa195_followup_research.zip'),
       '--candidate', str(ROOT/'tables/pa194C.tm'), '--output', str(out)]
subprocess.run(cmd, check=True)
print('Fresh census evidence:', out)
