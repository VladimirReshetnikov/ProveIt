#!/usr/bin/env python3
"""Deliberate malformed inputs and corrupt data must fail, also under -O."""
import argparse
import copy
import json
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from fractions import Fraction as F

import check_hypergraph as diagnostic
import derive_hierarchy as hierarchy
import rational_checks as rational
from validation import require, write_json, decimal_string

ROOT = Path(__file__).resolve().parent


def serialization_regressions():
    """Fixed-limit child processes keep this evidence independent of parent settings."""
    flags = ['-O'] if sys.flags.optimize else []
    evidence = []
    probe = r"""
import json, sys
sys.path.insert(0,sys.argv[1])
limit=int(sys.argv[2])
if sys.get_int_max_str_digits()!=limit:
    raise ArithmeticError("Unexpected initial digit limit")
from fractions import Fraction
from validation import decimal_string, json_output, require
import rational_checks as r
require(sys.get_int_max_str_digits()==limit,"Import changed digit limit")
huge=10**5000+123
expected="1"+"0"*4997+"123"
require(decimal_string(huge)==expected,"Positive large integer serialization")
require(decimal_string(-huge)=="-"+expected,"Negative large integer serialization")
require(decimal_string(0)=="0","Canonical zero serialization")
require(decimal_string(10**36+1)=="1"+"0"*35+"1","Internal zero chunk padding")
require(decimal_string(-7)=="-7","Canonical sign serialization")
require(r.rational(Fraction(huge,huge+2))==expected+"/"+"1"+"0"*4997+"125",
        "Large rational numerator and denominator serialization")
encoded=json_output({"negative":-huge,"positive":huge,"zero":0})
decoded=json.loads(encoded,parse_int=str)
require(decoded=={"negative":"-"+expected,"positive":expected,"zero":"0"},
        "Large numeric JSON output")
ordinary={"empty":[],"nested":[True,None,{"quote":"a\"b","unicode":"λ"}],"zero":0}
require(json_output(ordinary)==json.dumps(ordinary,sort_keys=True,indent=2),
        "JSON formatting compatibility")
rejected=0
for invalid in [True,False,1.5,Fraction(1,2),"0","0007","+7","-0","--7","7x",""]:
    try:
        decimal_string(invalid)
    except ValueError:
        rejected+=1
    else:
        raise ArithmeticError("Noninteger serializer input accepted")
# Generic external-input parsing must keep its interpreter guard.
for parse in [int,json.loads]:
    try:
        parse("9"*(limit+1))
    except ValueError:
        rejected+=1
    else:
        raise ArithmeticError("Generic input digit guard bypassed")
# Exercise certify's output-only comparison without a large decimal parser.
# This synthetic interval tests serialization plumbing, not a pole theorem.
original_exact,original_evaluate=r.exact_h,r.evaluate
context=r.Context(64)
recovery={"d":2,"n":2,"bits":64,"cutoff_method":"no_log","nearest_integer":expected}
noncanonical_rejections=0
try:
    r.exact_h=lambda d,n:huge
    r.evaluate=lambda d,n,M,bits:(context.exact(huge),{})
    synthetic=r.certify(2,2,recovery)
    require(synthetic["H"]==expected and synthetic["nearest_integer"]==expected,
            "Large cross-check serialization")
    require(len(synthetic["enclosure_lower_numerator"])>5000,
            "Synthetic interval did not exercise large endpoints")
    for bad in ["+"+expected,"0"+expected,"--"+expected,expected+"x"]:
        try:
            r.certify(2,2,{**recovery,"nearest_integer":bad})
        except ArithmeticError:
            noncanonical_rejections+=1
        else:
            raise ArithmeticError("Noncanonical recovered decimal accepted")
finally:
    r.exact_h,r.evaluate=original_exact,original_evaluate
require(sys.get_int_max_str_digits()==limit,"Serialization changed digit limit")
print(json.dumps({"requested_limit":limit,"computed_integer_digits":len(expected),
                  "serializer_and_input_rejections":rejected,
                  "process_limit_unchanged":True,"canonical_decimal_output":True,
                  "rational_and_numeric_json_passed":True,
                  "synthetic_cross_check_serialization_passed":True,
                  "noncanonical_computed_result_rejections":noncanonical_rejections},sort_keys=True))
"""
    with tempfile.TemporaryDirectory() as temporary:
        directory=Path(temporary)
        for limit,n in [(640,150),(4300,600)]:
            env=os.environ.copy()
            env['PYTHONINTMAXSTRDIGITS']=str(limit)
            tested=subprocess.run([sys.executable,'-B',*flags,'-c',probe,str(ROOT),str(limit)],
                                  env=env,capture_output=True,text=True,check=False)
            require(tested.returncode==0,"Serialization probe failed: "+tested.stderr)
            item=json.loads(tested.stdout)
            target=directory/f'recover_{n}.json'
            completed=subprocess.run([sys.executable,'-B',*flags,str(ROOT/'rational_checks.py'),
                                      'recover','2',str(n),'--output',str(target)],
                                     env=env,capture_output=True,text=True,check=False)
            require(completed.returncode==0,"Large-output recovery failed: "+completed.stderr)
            output_bytes=target.read_bytes()
            require(completed.stdout.encode('utf-8')==output_bytes,
                    "CLI stdout and saved output differ")
            recovered=json.loads(output_bytes)
            require(recovered['d']==2 and recovered['n']==n and
                    recovered['uses_exact_h_for_refinement'] is False,
                    "Unexpected large-output recovery result")
            endpoint_digits=len(recovered['enclosure_lower_numerator'].lstrip('-'))
            require(endpoint_digits>limit,"Full-path test did not exceed the digit limit")
            blocked=subprocess.run([sys.executable,'-B',*flags,str(ROOT/'rational_checks.py'),
                                    'recover','9'*(limit+1),'2'],env=env,
                                   capture_output=True,text=True,check=False)
            require(blocked.returncode!=0 and 'invalid int value' in blocked.stderr,
                    "CLI external input digit guard bypassed")
            item.update({"recovery_d":2,"recovery_n":n,
                         "recovery_output_sha256":hashlib.sha256(output_bytes).hexdigest(),
                         "endpoint_decimal_digits":endpoint_digits,
                         "nearest_integer_decimal_digits":len(recovered['nearest_integer']),
                         "stdout_matches_file":True,"CLI_input_guard_preserved":True})
            evidence.append(item)
    return evidence


def combined_driver_guard():
    """Low-cap diagnostic entry points must reject before creating output."""
    flags=['-O'] if sys.flags.optimize else []
    env=os.environ.copy()
    env['PYTHONINTMAXSTRDIGITS']='640'
    evidence=[]
    with tempfile.TemporaryDirectory() as temporary:
        directory=Path(temporary)
        for script,output_flag,name in [('reproduce.py','--output-dir','absent_directory'),
                                        ('check_hypergraph.py','--output','absent_file.json')]:
            destination=directory/name
            completed=subprocess.run([sys.executable,'-B',*flags,str(ROOT/script),
                                      output_flag,str(destination)],env=env,
                                     capture_output=True,text=True,check=False)
            require(completed.returncode!=0 and
                    'mpmath diagnostics require an integer-string digit limit of at least 4300'
                    in completed.stderr,"Diagnostic digit-limit preflight did not reject")
            require(not destination.exists(),"Rejected diagnostic entry point created output")
            evidence.append({"entry_point":script,"requested_limit":640,
                             "explicit_preflight_rejection":True,"output_created":False,
                             "interpreter_settings_changed":False})
    return evidence


def run(output):
    results = []

    def rejected(label, call, exception, fragment):
        try:
            call()
        except exception as error:
            require(fragment in str(error), f"Wrong guard for {label}: {error}")
            results.append({"case": label, "rejected": True,
                            "exception": exception.__name__, "guard": fragment})
        else:
            raise ArithmeticError(f"Guard failed: {label}")

    # Cached functions must not let booleans/floats reuse valid integer keys.
    rational.stirling_row(2)
    rational.fubini_list(2)
    rational.constant_bounds(8)
    bad = [
        ("d below domain", lambda: rational.recover(1, 5), ValueError, "d must"),
        ("negative n", lambda: rational.recover(2, -1), ValueError, "n must"),
        ("boolean d", lambda: rational.recover(True, 5), ValueError, "d must"),
        ("fractional n", lambda: rational.recover(2, F(5,2)), ValueError, "n must"),
        ("cutoff n=1", lambda: rational.cutoff(2, 1), ValueError, "n must"),
        ("zero retained cutoff", lambda: rational.evaluate(2, 5, 0, 64), ValueError, "M must"),
        ("zero precision", lambda: rational.Context(0), ValueError, "bits must"),
        ("boolean precision", lambda: rational.Context(True), ValueError, "bits must"),
        ("cached float Stirling input", lambda: rational.stirling_row(2.0), ValueError, "n must"),
        ("cached float Fubini input", lambda: rational.fubini_list(2.0), ValueError, "n must"),
        ("cached float constant precision", lambda: rational.constant_bounds(8.0), ValueError, "bits must"),
        ("unknown recovery method", lambda: rational.recover(2, 5,"unknown"), ValueError, "Unknown cutoff"),
        ("unknown tail method", lambda: rational.tail_budget(2,5,"unknown"), ValueError, "Unknown cutoff"),
        ("negative harmonic input", lambda: rational.harmonic(-1), ValueError, "n must"),
        ("invalid exact count domain", lambda: rational.exact_h(1, 5), ValueError, "d must"),
        ("invalid inclusion count domain", lambda: rational.inclusion_h(2, -1), ValueError, "n must"),
        ("derivation degree domain", lambda: hierarchy.data(1, 4), ValueError, "d must"),
        ("negative derivation order", lambda: hierarchy.data(2, -1), ValueError, "R must"),
        ("nonintegral derivation order", lambda: hierarchy.data(2, 2.0), ValueError, "R must"),
        ("diagnostic zero n", lambda: diagnostic.amplitude(2, 0, 1), ValueError, "n must"),
        ("diagnostic zero M", lambda: diagnostic.tail_bound(2, 3, 0), ValueError, "M must"),
        ("diagnostic invalid dimension", lambda: diagnostic.h_inclusion(1, 2), ValueError, "d must"),
        ("short Fubini table", lambda: diagnostic.h_stirling(2, 3, [1]), ValueError, "Fubini table"),
    ]
    for item in bad:
        rejected(*item)

    c, other = rational.Context(8), rational.Context(16)
    a, b = c.exact(1), other.exact(1)
    same_bits_other = rational.Context(8).exact(1)
    for label, call in [
        ("addition context mismatch", lambda: a+b),
        ("subtraction context mismatch", lambda: a-b),
        ("multiplication context mismatch", lambda: a*b),
        ("complex multiplication context mismatch", lambda: rational.cmul((a,a),(b,b))),
        ("distinct equal-precision contexts", lambda: a+same_bits_other),
    ]:
        rejected(label, call, ValueError, "context mismatch")
    for label, call, exception, fragment in [
        ("reversed dyadic endpoints", lambda: rational.Interval(c, 2, 1), ArithmeticError, "Reversed interval"),
        ("reversed Fraction bounds", lambda: c.from_bounds(F(2), F(1)), ArithmeticError, "Reversed rational bounds"),
        ("float endpoint", lambda: c.from_bounds(0.1, F(1)), ValueError, "Bounds must"),
        ("float exact input", lambda: c.exact(1.0), ValueError, "must be an integer"),
        ("float scale factor", lambda: a.scale_rational(0.5), ValueError, "Scale factor"),
        ("float rational output", lambda: rational.rational(0.5), ValueError, "Rational output"),
        ("float rounding input", lambda: rational.nearest_integer(0.5), ValueError, "Rounding input"),
        ("reciprocal crossing zero", lambda: c.from_bounds(F(-1),F(1)).reciprocal(), ArithmeticError, "positive interval"),
        ("reciprocal touching zero", lambda: c.from_bounds(F(0),F(1)).reciprocal(), ArithmeticError, "positive interval"),
    ]:
        rejected(label, call, exception, fragment)

    # File integrity tests use the same readers as the public computation CLI.
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        oeis = diagnostic.load_oeis(ROOT/'oeis_reference.json')
        coefficients = diagnostic.load_coefficients(ROOT/'hierarchy_reference.json')
        corrupted = copy.deepcopy(oeis)
        corrupted['3']['terms'][5] += 1
        p = directory/'oeis.json'
        write_json(p, corrupted)
        rejected("changed OEIS term", lambda: diagnostic.load_oeis(p), ValueError, "OEIS reference integrity mismatch")
        corrupted = copy.deepcopy(oeis)
        corrupted['2']['oeis'] = 'A173219'
        write_json(p, corrupted)
        rejected("wrong OEIS identifier", lambda: diagnostic.load_oeis(p), ValueError, "OEIS reference integrity mismatch")
        q = directory/'coefficients.json'
        corrupted = copy.deepcopy(coefficients)
        corrupted['2'][1] = 'z**2*(z**2 + 13)/192'
        write_json(q, corrupted)
        rejected("changed hierarchy coefficient", lambda: diagnostic.load_coefficients(q), ValueError, "Hierarchy coefficients integrity mismatch")
        corrupted = copy.deepcopy(coefficients)
        corrupted['4'].pop()
        write_json(q, corrupted)
        rejected("missing hierarchy order", lambda: diagnostic.load_coefficients(q), ValueError, "Hierarchy coefficients integrity mismatch")
        # Exercise CLI failure before any expensive diagnostic calculation.
        flags = ['-O'] if sys.flags.optimize else []
        for label, script, arguments, fragment in [
            ("CLI invalid recovery domain", 'rational_checks.py', ['recover','1','5'], 'd must'),
            ("CLI corrupt OEIS", 'check_hypergraph.py', ['--coefficients',str(ROOT/'hierarchy_reference.json'),'--oeis',str(p)], 'OEIS reference integrity mismatch'),
            ("CLI corrupt coefficients", 'check_hypergraph.py', ['--coefficients',str(q)], 'Hierarchy coefficients integrity mismatch'),
        ]:
            control_env=os.environ.copy()
            if script == 'check_hypergraph.py':
                # Test data corruption at the diagnostic layer's supported limit.
                control_env['PYTHONINTMAXSTRDIGITS']='4300'
            completed = subprocess.run([sys.executable,*flags,str(ROOT/script),*arguments],
                                       env=control_env,capture_output=True,text=True,check=False)
            require(completed.returncode != 0 and fragment in completed.stderr,
                    f"CLI guard failed: {label}")
            results.append({"case":label,"rejected":True,"guard":fragment})

    # Disable both exact-count oracles: pole recovery for n>=2 must still work.
    original_exact, original_fubini = rational.exact_h, rational.fubini_list
    def forbidden(*unused, **unused_keywords):
        raise ArithmeticError("An exact-count oracle was called during standalone recovery")
    try:
        rational.exact_h = forbidden
        rational.fubini_list = forbidden
        recovered = rational.recover(2, 25)
    finally:
        rational.exact_h, rational.fubini_list = original_exact, original_fubini
    require(recovered['nearest_integer'] == decimal_string(original_exact(2,25)),
            "Oracle-free recovery returned a wrong integer")
    require(len(recovered['precision_attempts']) > 1,
            "Oracle-free test did not exercise precision refinement")
    results.append({"case":"exact-count oracles disabled during precision refinement",
                    "passed":True,"precision_attempts":recovered['precision_attempts']})
    rational.interval_unit_checks()
    serializations=serialization_regressions()
    write_json(output,{"all_checks_passed":True,"negative_controls":results,
                       "fixed_limit_serialization_regressions":serializations,
                       "diagnostic_entry_point_digit_limit_guards":combined_driver_guard(),
                       "negative_control_count":sum(x.get('rejected',False) for x in results),
                       "oracle_independence_check_passed":True})
    print(json.dumps({"status":"PASS","negative_controls":len(results)-1,
                      "oracle_independence_check_passed":True},sort_keys=True))

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'negative_controls.json')
    run(parser.parse_args().output)
