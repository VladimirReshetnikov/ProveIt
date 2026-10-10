"""Portable package paths and deliberate, non-destructive output helpers."""
from pathlib import Path
import json

CODE_DIR = Path(__file__).resolve().parent
DATA_DIR = CODE_DIR.parent / 'data'


def read_json(name):
    return json.loads((DATA_DIR / name).read_text(encoding='utf-8'))


def write_new_or_compare(path, content):
    """Never replace a different existing artifact implicitly."""
    path = Path(path)
    if path.exists():
        if path.read_text(encoding='utf-8') != content:
            raise FileExistsError(f'Refusing to overwrite different existing content: {path}')
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding='utf-8')


def write_json_new_or_compare(path, data):
    write_new_or_compare(path, json.dumps(data, indent=2) + '\n')
