#!/usr/bin/env python3
"""Replay finite certificates, not the consistency of ZFC.

Python 3.10+ standard library only. All rebuilds run in a temporary copy.
The unbounded proofs and dependency boundaries are in report/report.pdf.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import argparse, hashlib, importlib.util, json, random, shutil, subprocess, sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "forms"))
from norm_dag import evaluate
from verify_final_forms import load_constants, evaluate_univariate
from build_forms import build
from build15_compact import build15


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    path = ROOT / "MANIFEST.json"
    if not path.exists():
        return {"status": "NOT_SEALED", "note": "Development replay before release manifest."}
    data = json.loads(path.read_text())
    for row in data["files"]:
        p = ROOT / row["path"]
        require(p.is_file(), "missing release file: " + row["path"])
        require(p.stat().st_size == row["bytes"] and sha(p) == row["sha256"],
                "release integrity mismatch: " + row["path"])
    return {"status": "PASS", "files": len(data["files"])}


def check_sources_and_constants():
    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for row in pins["inherited_files"]:
        require(sha(ROOT / row["file"]) == row["sha256"],
                "inherited source mismatch: " + row["file"])
    require(sha(ROOT / "upstream/parent_pell_congruences.zip") == pins["archive_sha256"],
            "parent archive mismatch")
    constants = load_constants(ROOT)
    require(constants == load_constants(ROOT / "forms"), "component coefficient copies differ")
    source = ROOT / "coefficients/source34/build_coefficients.py"
    spec = importlib.util.spec_from_file_location("native_fixed_constructor", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    values, audit = module.construct()
    aliases = {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}
    for name, old in aliases.items():
        require(values[old] == constants[name], "native reconstruction failed: " + name)
    require(constants["cone_A"] == 2**1113 and constants["cone_B"] == 2**666104,
            "determinant reconstruction failed")
    return constants, {"status": "PASS", "source_files": len(pins["inherited_files"]),
                       "large_numerals": 6, "native_audit": audit}


def expected_packets():
    result = []
    for n in (13, 14):
        for variant in ((False, True) if n == 13 else (False, True, "full", "half")):
            result.append(build(n, variant))
    result.append(build15())
    return result


def norm_mod(z, radicands, prime):
    """Independent multiplication in a formal multiquadratic algebra."""
    def multiply(left, right):
        out = {}
        for i, x in left.items():
            for j, y in right.items():
                value = x*y
                overlap = i & j
                while overlap:
                    bit = overlap & -overlap
                    value *= radicands[bit.bit_length()-1]
                    overlap ^= bit
                key = i ^ j
                out[key] = (out.get(key, 0) + value) % prime
        return {k: v for k, v in out.items() if v}
    terms = {0: z % prime, **{1 << i: prime-1 for i in range(len(radicands))}}
    for i in range(len(radicands)):
        other = {k: (-v if k & (1 << i) else v) % prime for k, v in terms.items()}
        terms = multiply(terms, other)
        require(not any(k & (1 << i) for k in terms), "independent norm root elimination failed")
    require(not any(terms), "independent norm is not scalar")
    return terms.get(0, 0)


def paper13_values(x, constants, prime):
    """Separately transcribed report Sections 2.2--2.3; does not read packet DEFS."""
    j,C,z,h,r,v,w,T,c,s,u1,u2,xi = (x[n] for n in
        ("j","C","z","h","r","v","w","T","c","s","p1","p2","xi"))
    beta,K0,MC,MF,A0,B0 = (constants[n] % prime for n in
        ("beta","K0","MC","MF","cone_A","cone_B"))
    J=6*j+1; q=beta*J+1; W=4*(3*w+1)
    F=(K0+W)*C-z*(q-1); X=q*W; Y=(2*v+1)*q**3
    R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J
    E=X*Y; a=E+Y; H=4*a+3; Delta=a*a+H
    k=R+1+h*E; eta=c-k*Y; zeta=k-eta; ell=E*k*Y
    I0=(2*r+1)*c*c; Df=1+Delta*I0*I0; Q=Delta*Delta*I0*I0
    delta=(Q-1) % prime; V=Df*(c*T-R)-c; D0=X+a*c
    Afirst=ell*(ell+k)+1; Dm=1+Delta*c*c
    G=A0*F*B0*C-(q-A0*F-B0*C)**2; Z=eta*zeta
    N=G*Z-(s*s-G-Z+1)**2
    S=24*N-21-(6*u1-1)**2-(6*u2-1)**2
    carrier=(D0+H*(xi+27*V)) % prime
    nums=[9*H*H*Afirst,81*H*H*Df,Dm,6561*H*H*S,729*H*H*(Q*V*V-1)]
    if delta == 0:
        return None
    rad=[n % prime for n in nums]
    rad[-1]=rad[-1]*pow(delta,-1,prime) % prime
    return pow(delta,16,prime)*norm_mod(carrier,rad,prime) % prime


def independent_article_check(packet, constants):
    rng = random.Random(1392475)
    checked = 0
    for prime in (1000000007, 1000000009):
        for _ in range(24):
            xs = {v: rng.randint(-7, 7) for v in packet["variables"]}
            expected = paper13_values(xs, constants, prime)
            if expected is None:
                continue
            actual = evaluate(packet, {**xs, **{n:v % prime for n,v in constants.items()}}, prime)
            require(actual == expected, "report-to-circuit transcription mismatch")
            checked += 1
    require(checked >= 40, "too few nonsingular independent transcription checks")
    return {"status":"PASS", "exact_modular_signed_assignments":checked,
            "scope":"Independent report transcription and multiquadratic norm evaluation; not an unbounded proof."}


def run_script(path, cwd):
    flags = ["-O"] if sys.flags.optimize else []
    result = subprocess.run([sys.executable, *flags, str(path)], cwd=cwd,
                            text=True, capture_output=True, timeout=120)
    require(result.returncode == 0, "replay failed: " + str(path.name) + "\n" + result.stdout + result.stderr)
    return {"script": path.name, "status":"PASS"}


def check_negative_controls(packet, constants, work):
    corrupted=deepcopy(packet)
    corrupted["nodes"][-1]["op"]="add" if corrupted["nodes"][-1]["op"]!="add" else "sub"
    require(json.dumps(corrupted,sort_keys=True) != json.dumps(build(13, True),sort_keys=True),
            "graph corruption was not detected")
    dead=deepcopy(packet);dead["inputs"].append("unbound_extra_input")
    caught=False
    try:
        evaluate_univariate(dead, constants)
    except RuntimeError:
        caught=True
    require(caught, "input corruption was not rejected")
    p=work/"forms/coefficients/payloads/MC.bin.gz";old=p.read_bytes()
    altered=bytearray(old);altered[-1]^=1;p.write_bytes(altered)
    caught=False
    try:
        load_constants(work/"forms")
    except RuntimeError:
        caught=True
    p.write_bytes(old)
    require(caught, "coefficient corruption was not rejected")
    return {"status":"PASS", "controls":["modified graph differs from literal builder",
            "extra input rejected", "changed coefficient byte rejected"]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,help="Optional receipt path; avoid overwriting sealed release files.")
    args=parser.parse_args()
    receipt={"status":"PASS", "python_optimization":sys.flags.optimize,
             "scope":"Finite algebra/data verification; the unbounded proof and inherited calibration are separate."}
    receipt["release_manifest"]=check_manifest()
    constants,receipt["coefficients_and_sources"]=check_sources_and_constants()
    packets=expected_packets();results=[]
    for expected in packets:
        path=ROOT/"forms"/(expected["name"]+".json")
        actual=json.loads(path.read_text())
        expected_bytes=(json.dumps(expected,indent=2)+"\n").encode()
        require(path.read_bytes() == expected_bytes, "literal generator mismatch: " + path.name)
        results.append(evaluate_univariate(actual,constants))
    receipt["equations"]=results
    main_packet=next(p for p in packets if p["name"]=="integer13_degree1392")
    receipt["independent_report_check"]=independent_article_check(main_packet,constants)
    with TemporaryDirectory(prefix="con_zfc_padic_replay_") as temp:
        work=Path(temp)
        shutil.copytree(ROOT/"forms",work/"forms",ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(ROOT/"code",work/"code",ignore=shutil.ignore_patterns("__pycache__"))
        receipt["independent_component_checks"]=[
            run_script(work/"forms/check_norm_dag.py",work/"forms"),
            run_script(work/"code/check_adapters.py",work/"code")]
        receipt["negative_controls"]=check_negative_controls(main_packet,constants,work)
    if args.output:
        target=args.output.resolve()
        require(target != ROOT/"MANIFEST.json", "cannot replace the manifest with a receipt")
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(json.dumps(receipt,indent=2)+"\n")
    print("PASS: 7 literal equations; native coefficients regenerated; independent norm/adapters and corruption controls.")
    for row in results:
        print(f"  {row['variable_count']} integers, degree {row['degree']}, {row['live_binary_operations']} live operations")
    print("Scope: finite certificate replay, not a consistency test or a kernel proof of the semantic compiler.")


if __name__=="__main__":
    main()
