#!/usr/bin/env python3
"""194-state specialization of the portable census (same CLI)."""
from pathlib import Path
import runpy,sys
sys.argv.extend(['--states','194'])
runpy.run_path(str(Path(__file__).with_name('census.py')),run_name='__main__')
