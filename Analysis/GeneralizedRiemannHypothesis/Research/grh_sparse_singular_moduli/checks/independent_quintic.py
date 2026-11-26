"""Independent multiplication-by-X recurrence and residue determinant replay."""
import json
import os
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
PLACES = [(601, 200), (1051, 350), (4201, 1400), (6301, 1050), (757, 252), (337, 112)]


def times_x(vector, polynomial, modulus):
    return tuple((a - b*vector[-1]) % modulus
                 for a, b in zip((0,) + vector[:-1], polynomial))


def times_vector(left, right, polynomial, modulus):
    # Horner evaluation of right(X) acting on left, with no coefficient convolution.
    result = (0,) * 5
    for coefficient in reversed(right):
        result = times_x(result, polynomial, modulus)
        result = tuple((v + coefficient*u) % modulus for v, u in zip(result, left))
    return result


def make_tables(path, polynomial):
    one = (1, 0, 0, 0, 0)
    for p, m in PLACES:
        value = one
        for _ in range(m):
            value = times_x(value, polynomial, p*p)
        assert value[0] % p and all(v % p == 0 for v in value[1:])
        derivative = (0,) + tuple(v//p for v in value[1:])
        with (path / f"{p}.dat").open("w") as out:
            print(m, file=out)
            value = one
            for _ in range(m):
                col = value
                for _ in range(5):
                    print(*col[1:], file=out)
                    col = times_vector(col, derivative, polynomial, p)
                value = times_x(value, polynomial, p)


def main():
    polynomial = json.loads((HERE.parent / "cm" / "class_polynomials.json").read_text())["-131"]
    with TemporaryDirectory() as dirname:
        path = Path(dirname)
        make_tables(path, polynomial)
        binary = path / "crosscheck"
        run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17",
             str(HERE / "independent_quintic.cpp"), "-o", str(binary)], check=True)
        run([str(binary)], cwd=path, check=True)


if __name__ == "__main__":
    main()
