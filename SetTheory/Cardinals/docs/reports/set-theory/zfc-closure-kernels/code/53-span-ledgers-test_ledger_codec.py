#!/usr/bin/env python3
"""Small independent round-trip/corruption checks for ledger_codec.py."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys
import tempfile

CODEC = Path(__file__).with_name("ledger_codec.py")
HEADER2 = "group\tdeleted\ta0\ta1\toutcome\tcase_or_needed\treason\tweight\n"
HEADERN = "group\tdeleted\tassignments\toutcome\tcase_or_needed\treason\tweight\n"


def invoke(*args, success=True):
    p = subprocess.run([sys.executable, str(CODEC), *map(str, args)], capture_output=True, text=True)
    assert (p.returncode == 0) == success, (args, p.returncode, p.stderr)
    return json.loads(p.stdout) if success else None


def main():
    fixtures = [
        (2, HEADER2 +
         "0\t7\t-1\t-1\tbranch\t0\t0\t0\n"
         "0\t7\t0\t-1\tbranch\t1\t0\t0\n"
         "0\t7\t0\t0\tprune\t17\t2\t1\n"
         "0\t7\t0\t1\tprune\t17\t2\t1\n"
         "0\t7\t1\t-1\tprune\t5\t3\t2\n"
         "1\t9\t-1\t-1\tbranch\t1\t0\t0\n"
         "1\t9\t-1\t0\tsurvivor\t-1\t0\t1\n"
         "1\t9\t-1\t1\tbranch\t0\t0\t0\n"
         "1\t9\t0\t1\tprune\t14\t1\t1\n"),
        (3, HEADERN +
         "0\t18\t-1\tbranch\t0\t0\t0\n"
         "0\t18\t0\tprune\t4\t1\t1\n"
         "0\t18\t1\tprune\t4\t1\t1\n"
         "0\t18\t2\tprune\t4\t1\t1\n"
         "1\t21\t-1,-1,-1\tbranch\t2\t0\t0\n"),
        (1008, HEADERN + "0\t18\t" + ",".join(["-1"] * 12) +
         f"\tprune\t7\t1\t{1008 ** 12}\n"),
        (251, HEADERN),
    ]
    with tempfile.TemporaryDirectory(prefix="proveit-ledger-tests-") as tmp:
        base = Path(tmp)
        for i, (choices, data) in enumerate(fixtures):
            raw, packed, restored = [base / f"fixture{i}.{s}" for s in ("tsv", "gz", "restored")]
            raw.write_bytes(data.encode())
            meta = invoke("pack", raw, packed, "--choices", choices)
            assert meta["raw_sha256"] == hashlib.sha256(data.encode()).hexdigest()
            invoke("verify", packed, "--raw", raw)
            invoke("unpack", packed, restored)
            assert restored.read_bytes() == data.encode()
            invoke("unpack", packed, restored, success=False)  # Refuse overwriting.
        # A malformed assignment order is detected by reconstructing the hash.
        bad = base / "bad.tsv"
        bad.write_text(fixtures[0][1].replace("0\t7\t0\t0\tprune", "0\t7\t9\t0\tprune"))
        invoke("pack", bad, base / "bad.gz", "--choices", 2, success=False)
        assert not (base / "bad.gz").exists()
        # A different action count changes the DFS and/or prune weights.
        invoke("pack", base / "fixture0.tsv", base / "wrong.gz", "--choices", 3, success=False)
        # A changed footer is rejected even when gzip's own checksum is valid.
        payload = bytearray(gzip.decompress((base / "fixture0.gz").read_bytes()))
        payload[-1] ^= 1
        (base / "corrupt.gz").write_bytes(gzip.compress(payload, mtime=0))
        invoke("verify", base / "corrupt.gz", success=False)
        # Missing final LF is not silently normalized.
        bad.write_bytes(fixtures[0][1].encode()[:-1])
        invoke("pack", bad, base / "unterminated.gz", "--choices", 2, success=False)
    print(json.dumps({"passed": True, "round_trip_fixtures": len(fixtures),
                      "checks": ["both headers", "changing group degrees", "partial final DFS",
                                 "repeated events", "survivor", "128-bit weight", "empty ledger",
                                 "refuse overwrite", "wrong assignments", "wrong choices",
                                 "corrupt footer", "missing terminal LF"]}))


if __name__ == "__main__":
    main()
