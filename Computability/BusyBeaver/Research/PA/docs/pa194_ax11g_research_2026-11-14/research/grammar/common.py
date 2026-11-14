"""Portable initialization shared by the terminal-grammar experiments."""
from pathlib import Path
import json, sys, tempfile
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
MACHINE = PACKAGE / 'machine'
sys.path.insert(0, str(PACKAGE / 'construction/vendor'))
import compiler as c
import support as s

def tup(t):
    return tuple(map(tup, t)) if isinstance(t, list) else t

G = tup(json.loads((MACHINE / 'grammar.tree.json').read_text()))
ns = {k: tup(v) for k, v in json.loads((MACHINE / 'nodes.json').read_text()).items()}
raw0 = s.read_table(MACHINE / 'raw.native.tm')
c.machine = lambda: (raw0, [])
c.raw_nodes = lambda: ns
inc = ('leaf', 'inc', 1)
c.MACROS[(inc, inc)] = 99
c.MACROS[((inc, inc), (inc, inc))] = 190

def word(t):
    return word(t[0]) + word(t[1]) if c.isnode(t) else [t]

def subtrees(t):
    out = {t}
    if c.isnode(t):
        out |= subtrees(t[0]) | subtrees(t[1])
    return out

def replace_last(t, x):
    if c.isnode(t):
        return t[0], replace_last(t[1], x)
    assert t == 'node49'
    return x

def output_dir(path, prefix):
    result = Path(path) if path else Path(tempfile.mkdtemp(prefix=prefix))
    result.mkdir(parents=True, exist_ok=True)
    return result

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')
