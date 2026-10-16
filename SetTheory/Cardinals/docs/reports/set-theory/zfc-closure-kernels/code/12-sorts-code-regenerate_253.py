#!/usr/bin/env python3
"""Independently regenerate the published 253 table from 254 numeric data.

The original 254-state machine is Mira-Cult's. The reduction is the public
mira-emmy/busy-beaver PR20 construction, head 0d544f2a2e3c18f12278441a74b7879f31cbe856.
Only its mathematical data (four edits and the state bijection) are reused;
this inspection/regeneration implementation was written for this report.
Regeneration checks a table identity; it does not repeat the Coq proof.
"""
import argparse
from hashlib import sha256
from pathlib import Path

BASE_HASH = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
RESULT_HASH = "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"
SOURCE = "https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/tools/generate_candidate.py"
OLD_LABELS = (
    5, 97, 64, 112, 85, 28, 131, 40, 63, 38, 48, 56, 7, 31, 10, 44,
    14, 60, 20, 0, 2, 1, 4, 3, 6, 9, 13, 19, 29, 41, 58, 74,
    84, 96, 110, 111, 33, 128, 129, 130, 47, 148, 12, 121, 149, 107, 150, 27,
    18, 167, 17, 144, 145, 25, 170, 125, 171, 172, 32, 39, 92, 26, 82, 71,
    30, 201, 147, 21, 202, 203, 204, 45, 46, 57, 24, 93, 94, 34, 42, 43,
    169, 11, 175, 88, 113, 61, 62, 73, 36, 37, 108, 50, 49, 59, 15, 16,
    105, 102, 103, 23, 132, 76, 77, 78, 83, 53, 54, 55, 126, 127, 75, 22,
    123, 124, 119, 120, 35, 151, 86, 87, 89, 95, 69, 70, 72, 81, 68, 67,
    146, 141, 142, 143, 51, 52, 173, 98, 99, 100, 101, 104, 109, 65, 79, 80,
    168, 166, 66, 114, 115, 116, 117, 118, 122, 90, 91, 200, 133, 134, 135, 136,
    137, 138, 139, 140, 106, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162,
    163, 164, 165, 174, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
    188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 205, 206, 207, 208,
    209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
    225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
    241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
)
EDITS = {(3, 0): (0, "L", 48), (5, 0): (1, "R", 97),
         (5, 1): (1, "R", 64), (49, 1): (0, "R", 5)}


def generate(baseline):
    data = Path(baseline).read_bytes()
    if sha256(data).hexdigest() != BASE_HASH:
        raise ValueError("Wrong 254 baseline bytes")
    rows = {}
    for line in data.decode("ascii").splitlines():
        if line.startswith("#") or not line:
            continue
        q, read, write, move, target = line.split()
        key = (int(q), int(read))
        if key in rows:
            raise ValueError("Duplicate baseline row")
        rows[key] = (int(write), move, int(target))
    if set(rows) != {(q, b) for q in range(254) for b in (0, 1)}:
        raise ValueError("Baseline is not a complete 254-state binary table")
    mapping = {old: new for new, old in enumerate(OLD_LABELS)}
    if len(mapping) != 254 or set(mapping) != set(range(255)) - {8}:
        raise ValueError("Malformed published bijection")
    if any(rows[key] == action for key, action in EDITS.items()):
        raise ValueError("An advertised edit changes nothing")
    rows.update(EDITS)
    output = []
    for (old, read), (write, move, target) in rows.items():
        if old == 8:
            continue
        output.append((mapping[old], read, write, move, mapping[target]))
    # Preserve the published file's lexicographic state-number row ordering.
    output.sort(key=lambda r: (str(r[0]), r[1]))
    result = ("#! start 0\n" + "".join("%d %d %d %s %d\n" % row for row in output)).encode("ascii")
    if sha256(result).hexdigest() != RESULT_HASH:
        raise ValueError("Reconstructed bytes differ from the published 253 table")
    return result


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, default=root / "machines/zfc_254.tm")
    parser.add_argument("--output", type=Path, help="Write a regenerated copy at this explicit path")
    args = parser.parse_args()
    data = generate(args.baseline)
    if args.output:
        args.output.write_bytes(data)
    elif data != (root / "machines/zfc_253.tm").read_bytes():
        raise ValueError("Packaged 253 table is not the reconstructed table")
    print("253 table regenerated exactly; SHA-256 " + RESULT_HASH)


if __name__ == "__main__":
    main()
