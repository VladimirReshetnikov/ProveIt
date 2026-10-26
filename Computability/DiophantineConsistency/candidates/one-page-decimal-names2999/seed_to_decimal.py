"""HELD stage A: exact seed numeral only. Never typesets or evaluates P66."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
OUT = Path("/tmp/decimal-names2999-materialized-v1")
TEX = "candidates/one-page-parity-clause2999/equation.tex"
ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
OPENER = "\\begingroup\\fontsize{7.7}{8.2}\\selectfont\\ttfamily\n"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked(data, spec):
    need(len(data) == spec["bytes"], "parent bytes")
    need(digest(data) == spec["sha256"], "parent hash")
    return data


def decode_seed(seed):
    need(len(seed) == 436 and seed[0] != "0" and
         all(ch in ALPHABET for ch in seed), "seed syntax")
    value = 0
    for ch in seed:
        value = 62 * value + ALPHABET.index(ch)
    return value


def verify_decimal(text, seed):
    need(1 <= len(text) <= 872 and text[0] != "0" and
         all("0" <= ch <= "9" for ch in text), "decimal syntax")
    remaining = int(text, 10)
    reverse = []
    for _ in range(436):
        remaining, digit = divmod(remaining, 62)
        reverse.append(ALPHABET[digit])
    need(remaining == 0 and "".join(reversed(reverse)) == seed,
         "decimal value")


def rejected(function, value, message):
    try:
        function(value)
    except ValueError as error:
        need(str(error) == message, "wrong rejection")
        return
    raise ValueError("negative accepted")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    pins = json.loads((HERE / "SOURCE_PINS.json").read_text("ascii"))
    need(pins["schema"] == "decimal_names2999_seed_stage_A_v1" and
         len(pins["parent_files"]) == 9, "pins schema")
    parent = {}
    for relative, spec in pins["parent_files"].items():
        path = BASE / relative
        need(path.is_file() and not path.is_symlink(), "parent regular")
        parent[relative] = checked(path.read_bytes(), spec)
    tex = parent[TEX].decode("ascii")
    need(tex.count(ALPHABET) == 1 and tex.count(OPENER) == 1,
         "seed opener/alphabet")
    tail = tex.split(OPENER, 1)[1]
    need(tail.count("\\endgroup\n") == 1, "seed closer")
    lines = tail.split("\\endgroup\n", 1)[0].splitlines()
    need(len(lines) == 8 and all(line.endswith("\\par") for line in lines),
         "seed lines")
    seed = "".join(line[:-4] for line in lines)
    value = decode_seed(seed)
    decimal = str(value)
    need(int(decimal, 10) == value, "decimal parse")
    verify_decimal(decimal, seed)
    bad_last = decimal[:-1] + ("0" if decimal[-1] != "0" else "1")
    for bad, why in [("", "decimal syntax"), ("+1", "decimal syntax"),
                     ("0" + decimal, "decimal syntax"),
                     (bad_last, "decimal value"),
                     (decimal[:-1], "decimal value")]:
        rejected(lambda item: verify_decimal(item, seed), bad, why)
    for bad in [seed[:-1], seed + "0", "0" + seed[1:], "/" + seed[1:]]:
        rejected(decode_seed, bad, "seed syntax")
    rejected(lambda item: checked(item, pins["parent_files"][TEX]),
             b"!" + parent[TEX][1:], "parent hash")
    payload = (decimal + "\n").encode("ascii")
    receipt = {"schema": "decimal_names2999_seed_receipt_v1",
               "parent_TeX_sha256": digest(parent[TEX]),
               "base62_seed_sha256": digest(seed.encode("ascii")),
               "seed_characters": 436, "decimal_digits": len(decimal),
               "decimal_file_sha256": digest(payload),
               "negative_controls": 10, "valid_controls": 2,
               "scope": "Whole seed identity only; DAG/ports hashed only."}
    expected = {"decimal.txt": payload,
                "RECEIPT.json": (json.dumps(receipt, indent=2,
                                sort_keys=True) + "\n").encode("ascii")}
    if args.write:
        need(not OUT.exists() and not OUT.is_symlink(), "output exists")
        OUT.mkdir()
        for name, data in expected.items():
            with (OUT / name).open("xb") as handle:
                handle.write(data)
    need(OUT.is_dir() and not OUT.is_symlink(), "output directory")
    need(sorted(path.name for path in OUT.iterdir()) == sorted(expected),
         "output members")
    for name, data in expected.items():
        path = OUT / name
        need(path.is_file() and not path.is_symlink(), "output regular")
        need(path.read_bytes() == data, "output bytes")
    print(json.dumps({"ok": True, "written": args.write,
                      "optimized": not __debug__, **receipt}, sort_keys=True))


if __name__ == "__main__":
    main()
