#!/usr/bin/env python3
"""Owned phase23 entry point; source-only draft, not executed."""
from pathlib import Path
import hashlib,runpy
_adapter=Path(__file__).with_name('phase_adapter.py')
assert hashlib.sha256(_adapter.read_bytes()).hexdigest()=='109e2e0abbc169492af99907a137b634073736254751dabc01ed54c853cecb42'
runpy.run_path(str(_adapter),run_name='phase23_owned_adapter')['launch'](
 'actual',Path(__file__),'6398a6af29a8213a525517318c7c9de34fdc71f37f3d9b4669ebbef2e1ca7602','109e2e0abbc169492af99907a137b634073736254751dabc01ed54c853cecb42')
