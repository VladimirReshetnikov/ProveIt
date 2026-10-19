"""Minimal unchanged API extracted from ProveIt theory_backend_experiment.py.

Only published_spec and emit are needed by these searches. Their bodies are
unchanged. Repository backend imports and unrelated experiments are omitted.
The original full-file hash and retained fixture origins are in pins.json.
"""
import ast
import hashlib
from pathlib import Path
SNAPSHOT=Path(__file__).resolve().parents[1]/'fixtures/upstream'

def published_spec():
    """Load just pure AX formula definitions, with symbolic primitive codes.

    This parses the pinned reference as data; no import, IO or enumerator body
    from that file is run.  The independent AX stack executor supplies the other
    side of the comparison.
    """
    path = SNAPSHOT / "ZF/m254/tools/logic/spec.py"
    source = path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != "7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9":
        raise ValueError("published symbolic spec differs from the pinned version")
    tree = ast.parse(source)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                 and n.name not in ("_code", "enum_step")]
    module = ast.Module(body=functions, type_ignores=[])
    namespace = {"F": 1, "_code": lambda tag, a, b:
                 (("imp", "rel", "all", "eq")[tag], a, b)}
    exec(compile(module, str(path), "exec"), namespace)
    return namespace, digest

def emit(formula):
    if formula == "a": return [166]
    if formula == "b": return [121]
    if formula == "c": return [168]
    if formula == "u": return [171, 158, 208]
    if formula == 0: return [171]
    if formula == 1: return [177]
    # Recognize the published derived constructors before ordinary implication.
    if (isinstance(formula, tuple) and formula[0] == "imp"
            and formula[2] == 1):
        inner = formula[1]
        if (isinstance(inner, tuple) and inner[0] in ("imp", "all")
                and isinstance(inner[2], tuple) and inner[2][0] == "imp"
                and inner[2][2] == 1):
            macro = 178 if inner[0] == "imp" else 183
            return emit(inner[1]) + emit(inner[2][1]) + [macro]
        return emit(inner) + [218]
    kind, left, right = formula
    macro = {"imp": 119, "rel": 181, "eq": 182, "all": 180}[kind]
    return emit(left) + emit(right) + [macro]
