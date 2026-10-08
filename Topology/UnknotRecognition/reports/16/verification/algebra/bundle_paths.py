"""Locate both packaged implementations without installing either package.

The production package keeps its normal ``fastunknot`` name.  The immutable
baseline is imported under a private package name so the two implementations
cannot accidentally replace each other's modules in sys.modules.
"""
from __future__ import annotations

import importlib
import sys
import types
from pathlib import Path


BUNDLE_ROOT = Path(__file__).resolve().parents[2]
IMPLEMENTATION_FAST = BUNDLE_ROOT / "implementation" / "fast"
BASELINE_FAST = BUNDLE_ROOT / "baseline" / "fast"
HERE = Path(__file__).resolve().parent
_BASELINE_PACKAGE = "_unknot_algebra_baseline"


def implementation_path() -> Path:
    if not (IMPLEMENTATION_FAST / "fastunknot" / "dense_compose.py").is_file():
        raise FileNotFoundError("The bundle's implementation/fast/fastunknot/dense_compose.py is missing")
    path = str(IMPLEMENTATION_FAST)
    if path not in sys.path:
        sys.path.insert(0, path)
    return IMPLEMENTATION_FAST


def baseline_module(name: str):
    package_dir = BASELINE_FAST / "fastunknot"
    if not (package_dir / "planar.py").is_file():
        raise FileNotFoundError("The bundle's baseline/fast/fastunknot/planar.py is missing")
    if _BASELINE_PACKAGE not in sys.modules:
        # Import only the requested baseline modules, without executing an
        # unrelated top-level recognizer import from the package __init__.
        package = types.ModuleType(_BASELINE_PACKAGE)
        package.__path__ = [str(package_dir)]
        package.__package__ = _BASELINE_PACKAGE
        package.__file__ = str(package_dir / "__init__.py")
        sys.modules[_BASELINE_PACKAGE] = package
    return importlib.import_module(f"{_BASELINE_PACKAGE}.{name}")


implementation_path()
