"""Independent five-term certificates for discriminants -87 and -348.

Run from the archive root: python3 checks/fast_sieve/verify.py
The input is the same class-polynomial data certified by verify_five_small.py.
"""
import json
from math import isqrt
import os
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from table_builder import prepare

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE.parent/"five_small_witnesses.json").read_text())


def count(path):
    with path.open() as f:
        return sum(1 for _ in f)


with TemporaryDirectory() as tmp:
    work = Path(tmp)
    for name in ("collide", "join"):
        run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17",
             str(HERE/f"{name}.cpp"), "-o", str(work/name)], check=True)
    for d in (87, 348):
        H = DATA[str(d)]["coefficients"]
        assert H is not None and len(H) == 7 and H[-1] == 1
        primes = [(487,486),(1459,486)]
        if d == 87:
            primes += [(103,102),(151,150),(1531,1530)]
        for p,m in primes:
            assert all(p % k for k in range(2,isqrt(p)+1))
            prepare(H,p,m,work/f"p{p}")
        stages = [(487,1459,486,196587 if d==87 else 0)]
        if d == 87:
            stages += [(103,103,102,13125),(151,151,150,19669)]
        for p,q,m,expected in stages:
            path = work/f"r{m}"
            with path.open("w") as f:
                run([work/"collide",work/f"p{p}",work/f"p{q}"],stdout=f,check=True)
            assert count(path) == expected
        if d == 87:
            result = run([work/"join",work/"r102",work/"r486",work/"r150",
                          work/"p1531"],capture_output=True,text=True,check=True)
            assert not result.stdout
            expected = "candidate lifts 653917425, signature-compatible 979524, surviving 0"
            assert result.stderr.strip() == expected
            print(expected, flush=True)
        print(f"-{d}: no compatible exponent quadruple", flush=True)
