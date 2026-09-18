"""Cross-check the Rust binary against the Python package on random braid closures.

Usage:  python cross_check.py [count]   (run after `cargo build --release`)
Compares reduced ranks, ranks by cube degree, and recognition verdicts.
"""
import json, os, random, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "fast"))
from fastunknot import Diagram, khovanov_rank, recognize  # noqa: E402

BINARY = os.path.join(HERE, "target", "release", "fastunknot.exe" if os.name == "nt" else "fastunknot")


def rust(command, data, *options):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
        json.dump(data, handle)
    try:
        out = subprocess.run([BINARY, command, handle.name, *options], capture_output=True, text=True)
        return json.loads(out.stdout)
    finally:
        os.unlink(handle.name)


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    rng = random.Random(2026)
    checked = problems = 0
    while checked < count:
        strands = rng.choice([2, 3, 4, 5, 6])
        word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(rng.randint(1, 16))]
        try:
            d = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        checked += 1
        data = {"braid": {"strands": strands, "word": word}}
        expected = khovanov_rank(d.pd)
        for options in ([], ["--lifo"], ["--tail", "1"]):
            got = rust("khovanov", data, *options)
            by_degree = {int(h): 2 * v for h, v in got["reduced_by_degree"].items()}
            if got["reduced_rank"] != expected["reduced_rank"] or by_degree != expected["by_degree"]:
                problems += 1
                print("RANK MISMATCH", data, options, got["reduced_rank"], expected["reduced_rank"])
        for options, kwargs in (([], {}), (["--no-jones", "--no-modular"], {"use_jones": False, "use_alexander": False})):
            got = rust("recognize", data, *options)
            want = recognize(d, **kwargs)
            if got["status"] != want.status:
                problems += 1
                print("VERDICT MISMATCH", data, options, got["status"], want.status)
    print(f"checked {checked} braid closures, {problems} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
