"""Small input and integrity guards, active with and without python -O."""
import hashlib
import json
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def integer(name, value, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def domain(d, n, minimum_n=0):
    integer("d", d, 2)
    integer("n", n, minimum_n)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def load_pinned_json(path, expected_digest, label):
    value = json.loads(Path(path).read_text(encoding="utf-8"))
    if digest(value) != expected_digest:
        raise ValueError(f"{label} integrity mismatch")
    return value


def write_json(path, value):
    Path(path).write_text(json_output(value) + "\n", encoding="utf-8")


def decimal_string(value):
    """Serialize a computed integer without changing Python's input digit cap.

    Conversion is in base 10**18, so built-in str() sees at most 18 decimal
    digits at a time. This accepts integers only; it is not an input parser.
    """
    if type(value) is not int:
        raise ValueError("Decimal output requires an integer")
    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    value = abs(value)
    base, chunks = 10**18, []
    while value >= base:
        value, remainder = divmod(value, base)
        chunks.append(str(remainder).rjust(18,"0"))
    return sign + str(value) + "".join(reversed(chunks))


def json_output(value):
    """Deterministic output-only JSON, including arbitrarily large integers.

    Equivalent to json.dumps(value, indent=2, sort_keys=True) on the
    supported JSON types. String escaping still uses the standard encoder.
    Input json.loads/int behavior and interpreter settings are untouched.
    """
    def render(item, level):
        if item is None:
            return "null"
        if type(item) is bool:
            return "true" if item else "false"
        if type(item) is int:
            return decimal_string(item)
        if type(item) is str:
            return json.dumps(item)
        if type(item) is float:
            return json.dumps(item, allow_nan=False)
        prefix = "  "*(level+1)
        suffix = "  "*level
        if type(item) in (list,tuple):
            if not item:
                return "[]"
            return "[\n" + ",\n".join(prefix+render(x,level+1) for x in item) + "\n" + suffix+"]"
        if type(item) is dict:
            if any(type(key) is not str for key in item):
                raise ValueError("JSON output keys must be strings")
            if not item:
                return "{}"
            return "{\n" + ",\n".join(prefix+json.dumps(key)+": "+render(item[key],level+1)
                                      for key in sorted(item)) + "\n" + suffix+"}"
        raise ValueError("Unsupported JSON output type")
    return render(value,0)


def require_diagnostic_digit_limit():
    """Check the pinned mpmath diagnostic requirement without changing settings."""
    digit_limit=sys.get_int_max_str_digits()
    require(digit_limit == 0 or digit_limit >= 4300,
            'mpmath diagnostics require an integer-string digit limit of at least 4300 '
            '(or an already unlimited interpreter). No interpreter settings were changed. '
            'Standalone rational_checks.py recover remains supported at 640.')
