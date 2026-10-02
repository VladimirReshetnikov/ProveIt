"""Validate output destinations and write generated JSON without touching source."""

import json
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ENVIRONMENT_VARIABLE = "TIED_FOOTBALL_OUTPUT_DIR"
PROTECTED_DIRECTORIES = ("expected", "code", "report")


def output_directory(path=None):
    """Resolve and validate an output directory, including symbolic links."""
    selected = path if path is not None else os.environ.get(
        OUTPUT_ENVIRONMENT_VARIABLE, str(ROOT / "replay_outputs")
    )
    lexical = Path(os.path.abspath(Path(selected).expanduser()))
    resolved = lexical.resolve()
    if resolved == ROOT or lexical == ROOT:
        raise ValueError("The package root cannot be used as an output directory")
    for name in PROTECTED_DIRECTORIES:
        protected = ROOT / name
        for candidate in (lexical, resolved):
            for boundary in (protected, protected.resolve()):
                if candidate == boundary or candidate.is_relative_to(boundary):
                    raise ValueError(f"Output directory must not be inside {name}/")
    if resolved.exists() and not resolved.is_dir():
        raise ValueError("Output destination exists and is not a directory")
    return resolved


def write_result(name, result):
    """Atomically replace one generated result, never following a file symlink."""
    if not name or any(character not in "abcdefghijklmnopqrstuvwxyz_0123456789" for character in name):
        raise ValueError("Invalid result name")
    directory = output_directory()
    directory.mkdir(parents=True, exist_ok=True)
    # Check again after creation in case a directory component is a symlink.
    directory = output_directory(directory)
    destination = directory / f"{name}.json"
    # Refuse explicit symlink destinations even though atomic replacement
    # would replace the link itself rather than following it.
    if destination.is_symlink():
        raise ValueError("A generated output file must not be a symbolic link")
    payload = json.dumps(result, indent=2, allow_nan=False) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{name}.", suffix=".tmp", dir=directory)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(payload)
        os.replace(temporary_name, destination)
    finally:
        Path(temporary_name).unlink(missing_ok=True)
    return destination
