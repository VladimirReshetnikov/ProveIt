"""Read pinned inputs from the placed PA194 and PA195 research packets.

The digests are SHA-256 values of members of the original incoming archives.
Their reference copies of Program.lean were not retained when unpacking; the
byte-identical tracked upstream copy is used for that member. Native tables
removed as renamed duplicates are reconstructed from their pinned dense tables
and state maps and checked against the original member hashes.
"""
from hashlib import sha256
import json
from pathlib import Path

# Original archive member names and hashes, independently checked against both
# the former archive bytes and their replacements in the tracked tree.
_PINS = {
    ('194', 'pa194_conpa/construction/tables/pa194.tm'): '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f',
    ('194', 'pa194_conpa/construction/tables/unfolded201.native.tm'): 'b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87',
    ('194', 'pa194_conpa/construction/tables/pa194.native.tm'): 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54',
    ('194', 'pa194_conpa/construction/tables/pa194.labels.json'): 'b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964',
    ('194', 'pa194_conpa/construction/source/pa194.folds.json'): '61a99ee97d711ea436706f76383f1c283d4bb8f135c04b75ca35e2f0fb9612f0',
    ('194', 'pa194_conpa/construction/evidence/pa194.local-cases.json'): '4209dea78141fc38625926ab86019878a8eb6f6573f42845ca33adf28e19e93d',
    ('194', 'pa194_conpa/construction/source/pa194.grammar.json'): 'ca78fcfb8394f09eea1ed0d2fdf8fbabd8b4f5ac524f742ba9c45f4b69c1915f',
    ('194', 'pa194_conpa/construction/reference/PA196/Program.lean'): '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872',
    ('195', 'pa195_conpa/pa195/pa195.tm'): '5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455',
    ('195', 'pa195_conpa/pa195/unfolded202.native.tm'): '053d343528b2ec453163b84817fa0bcb12162184732950874db537db61c1fb88',
    ('195', 'pa195_conpa/pa195/pa195.native.tm'): '061476b12943116f3228d4d3ef251c2be420dad213cef452b1ff122c9a2b0aea',
    ('195', 'pa195_conpa/pa195/labels.json'): '95ceab2cd67aee6c4cd6822800e753979d005488d408d5c8c35accb46410b987',
    ('195', 'pa195_conpa/pa195/folds.json'): '7bac1a3ac9682978b452bf2f9eabdac62046b265f5cdabd680ddb49beee65b16',
    ('195', 'pa195_conpa/pa195/local_fold_certificate.json'): 'a34c8ef0783b304decfdd092c1924306150fd44f8db7e7ae4dfdb6778a8740a5',
    ('195', 'pa195_conpa/pa195/grammar.json'): 'b5a4f7beb6a7342ef3f50e949c4b896861e0de4876f8d70e15e8071e6d81ce5f',
    ('195', 'pa195_conpa/pa195/source.json'): 'd35c2d718f07dd80892f42e0b78f9e6a21f05aa0521cdc779a7dadade502df69',
    ('195', 'pa195_conpa/pa195/vendor/reference/PA196/Program.lean'): '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872',
}


class PlacedPacket:
    """Archive-like reader limited to explicitly pinned packet members."""

    def __init__(self, repo, machine):
        self.repo = Path(repo)
        self.machine = str(machine)
        if self.machine not in ("194", "195"):
            raise ValueError("unknown packet")

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False

    def read(self, member):
        expected = _PINS.get((self.machine, member))
        if expected is None:
            raise ValueError(f"unrecognized pinned packet member: {member}")
        native = {
            "194": ("pa194_conpa/construction/tables/pa194.native.tm",
                    "pa194_conpa/construction/tables/pa194.tm",
                    "pa194_conpa/construction/tables/pa194.labels.json"),
            "195": ("pa195_conpa/pa195/pa195.native.tm",
                    "pa195_conpa/pa195/pa195.tm",
                    "pa195_conpa/pa195/labels.json"),
        }[self.machine]
        if member == native[0]:
            # The native table was removed as a state-renamed duplicate. Recreate
            # its original sorted bytes from the independently pinned dense table
            # and state map, then verify the original member hash below.
            dense = self.read(native[1]).decode('ascii')
            labels = json.loads(self.read(native[2]))
            rows = []
            for line in dense.splitlines():
                q, bit, write, direction, target = line.split()
                rows.append((labels[int(q)], int(bit), int(write), direction,
                             labels[int(target)]))
            rows.sort(key=lambda row: (row[0], row[1]))
            data = ''.join(f'{q} {bit} {write} {direction} {target}\n'
                           for q, bit, write, direction, target in rows).encode('ascii')
            if sha256(data).hexdigest() != expected:
                raise ValueError(f"packet member SHA-256 mismatch: {member}")
            return data
        base = self.repo / "Computability/BusyBeaver/Research/PA"
        if member.endswith("/reference/PA196/Program.lean"):
            path = base / "jamesyc-upstream/pa196/PA196/Program.lean"
        else:
            prefix = f"pa{self.machine}_conpa/"
            if not member.startswith(prefix):
                raise ValueError("packet member prefix mismatch")
            path = base / "docs" / f"pa{self.machine}_conpa_2026-11-13" / member[len(prefix):]
        data = path.read_bytes()
        if sha256(data).hexdigest() != expected:
            raise ValueError(f"packet member SHA-256 mismatch: {member}")
        return data
