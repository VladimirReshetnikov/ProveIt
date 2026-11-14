#!/usr/bin/env python3
"""Replay the cached-head command algebra without modifying frozen references."""
from pathlib import Path
import importlib.util
import json

ROOT = Path(__file__).resolve().parents[1]
path = ROOT / 'reference/cached/check_composite_commands.py'
spec = importlib.util.spec_from_file_location('cached_commands', path)
module = importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name] = module
spec.loader.exec_module(module)
if not __debug__: raise SystemExit('Use Python without -O.')
result = module.verify_family('separate196', 10)
assert result['symbolic_cases'] == 188
print(json.dumps(result, indent=2))
