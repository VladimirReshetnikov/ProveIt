#!/usr/bin/env python3
"""Run exact verifier in normal/-O modes, then independently corrupt equations/data.

All corruption is confined to temporary copies. A test is accepted only if the
verifier exits nonzero in BOTH modes and reports the intended failure phase and
diagnostic. The untouched committed files are rechecked at the end. Runtime and
file hashes are operational metadata, not mathematical floating-point checks.
"""
import ast
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
VERIFIER=HERE/"verify_exact.py"
FIXTURES=HERE/"fixtures.json"
EXPECTED=HERE/"expected_summary.json"
LOGS=HERE/"logs"


def require(condition,message):
    if not condition:
        raise RuntimeError(message)


def pointer_get(data,path):
    for part in path:
        data=data[part]
    return data


def pointer_set(data,path,value):
    parent=pointer_get(data,path[:-1])
    parent[path[-1]]=value


def add_rational(value):
    return str(F(value)+1)


def execute(script,fixture,opt,name):
    argv=[sys.executable]+(["-O"] if opt else [])+[str(script),"--fixtures",str(fixture),"--expected-summary",str(EXPECTED)]
    completed=subprocess.run(argv,text=True,capture_output=True,timeout=30)
    LOGS.mkdir(exist_ok=True)
    suffix="optimized" if opt else "normal"
    (LOGS/(name+"."+suffix+".stdout")).write_text(completed.stdout,encoding="utf-8")
    (LOGS/(name+"."+suffix+".stderr")).write_text(completed.stderr,encoding="utf-8")
    payload=json.loads(completed.stdout if completed.returncode==0 else completed.stderr)
    return {"python_optimization":opt,"returncode":completed.returncode,"payload":payload,
            "stdout_log":"logs/"+name+"."+suffix+".stdout",
            "stderr_log":"logs/"+name+"."+suffix+".stderr"}


def main():
    original_fixture=FIXTURES.read_bytes()
    original_source=VERIFIER.read_bytes()
    base=json.loads(original_fixture)
    require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(original_source))),
            "Verifier must have no assertion correctness gates")
    records=[]
    baseline=[]
    for opt in (0,1):
        result=execute(VERIFIER,FIXTURES,opt,"baseline")
        require(result["returncode"]==0 and result["payload"]["status"]=="passed","baseline failed")
        baseline.append(result)
    # M=3,r=1/2, w=1/10. These mutations are independent copies of the baseline.
    i=next(k for k,c in enumerate(base["frozen_cases"]) if c["M"]==3 and c["r"]=="1/2")
    z=next(k for k,c in enumerate(base["frozen_cases"]) if c["M"]==3 and c["r"]=="1")
    C=["frozen_cases",i]
    W=C+["weights",0]
    Z=["frozen_cases",z]
    # A generic data hash is checked only AFTER these equation checks. Each
    # mathematical mutation must fail at its specific equation, not at the hash.
    data_mutations=[
      ("unweighted_lambda",C+["lambda"],add_rational,"frozen_exact_algebra","unweighted_eigenvalue_formula"),
      ("unweighted_eigenvector",C+["f",1],add_rational,"frozen_exact_algebra","rational_parametrization"),
      ("geometric_probability",C+["p",1],add_rational,"frozen_exact_algebra","geometric_kernel"),
      ("normalized_b",C+["b_scaled",1],add_rational,"frozen_exact_algebra","normalized_b_finite_sums"),
      ("normalized_c",C+["c_scaled"],add_rational,"frozen_exact_algebra","normalized_c_stationary_mean"),
      ("normalized_h",C+["h_scaled",2],add_rational,"frozen_exact_algebra","normalized_corrector_stable_formula"),
      ("weighted_lambda",W+["lambda_w"],add_rational,"frozen_exact_algebra","weighted_eigenvalue_shift"),
      ("weighted_denominator",W+["d_w"],add_rational,"frozen_exact_algebra","weighted_denominator"),
      ("signed_delta",W+["delta_w"],lambda x:str(-F(x)),"frozen_exact_algebra","signed_delta_formula"),
      ("weighted_negative_entry",W+["p_w",1],lambda x:str(-F(x)),"frozen_exact_algebra","weighted_strict_positivity"),
      ("weighted_positive_entry",W+["p_w",1],add_rational,"frozen_exact_algebra","weighted_stochastic_rows"),
      ("weighted_first_moment",W+["scaled_first_moment",1],add_rational,"frozen_exact_algebra","weighted_first_moment_fixture"),
      ("weighted_increment_moment",W+["increment_moments",2],add_rational,"frozen_exact_algebra","weighted_increment_moments"),
      ("weighted_tracker_drift",W+["tracker_drift",1],add_rational,"frozen_exact_algebra","weighted_tracker_drift"),
      ("q0_normalized_limit",Z+["h_scaled",2],add_rational,"frozen_exact_algebra","normalized_corrector_stable_formula"),
      ("q0_weighted_data",Z+["weights",0,"lambda_w"],add_rational,"frozen_exact_algebra","weighted_eigenvalue_shift"),
      ("transition_coefficient",["level_polynomials",7,3],lambda x:x+1,"transition_polynomials","incoming transition polynomial n=7"),
      ("fishburn_value",["zero_level","fishburn",11],lambda x:x+1,"zero_level_transform","ordinary Fishburn prefix recurrence"),
      ("primitive_value",["zero_level","primitive",11],lambda x:x+1,"zero_level_transform","primitive ascent prefix recurrence"),
      ("inverse_transform_sign",["zero_level","inverse_transform_rows",10,1],lambda x:-x,"zero_level_transform","inverse binomial summand n=11, j=1"),
    ]
    source=original_source.decode("utf-8")
    source_mutations=[
      ("equation_weighted_eigen_drop_w",
       'sum((v if j>=l else 1)*(w if j==l else 1)*f[j] for j in range(M))==lamw*f[l]',
       'sum((v if j>=l else 1)*f[j] for j in range(M))==lamw*f[l]',
       "frozen_exact_algebra","weighted_eigen_rows"),
      ("equation_signed_mixture_plus",
       'Pw[l][j]==(1-delta)*P[l][j]+delta*int(j==l)',
       'Pw[l][j]==(1+delta)*P[l][j]+delta*int(j==l)',
       "frozen_exact_algebra","signed_algebraic_mixture_entries"),
      ("equation_weighted_poisson_sign",
       'ph_difference==(c-b[l])/dw',
       'ph_difference==(b[l]-c)/dw',
       "frozen_exact_algebra","weighted_poisson_operator_rows"),
      ("equation_tracker_sign",
       'inc==1-F((j-l)%M,M)+F(a*j,M*(M+a))',
       'inc==1-F((j-l)%M,M)-F(a*j,M*(M+a))',
       "frozen_exact_algebra","tracker_transition_identity"),
      ("equation_q0_lambda_endpoint",
       'check("q0_weighted_eigenvalue",lamw==M+w-1,cx)',
       'check("q0_weighted_eigenvalue",lamw==M+w,cx)',
       "frozen_exact_algebra","q0_weighted_eigenvalue"),
      ("equation_transition_level_shift",
       'coeff[e+1]+=value',
       'coeff[e]+=value',
       "transition_polynomials","incoming transition polynomial n=2"),
      ("equation_zero_transform_index",
       '(-1)**j*comb(n-1,j)*fishburn[n-j]',
       '(-1)**j*comb(n,j)*fishburn[n-j]',
       "zero_level_transform","inverse binomial summand n=2, j=1"),
    ]
    with TemporaryDirectory(prefix="report107-corruption-") as td:
        temp=Path(td)
        def test(name,kind,script,fixture,phase,diagnostic,change):
            outcomes=[]
            for opt in (0,1):
                result=execute(script,fixture,opt,name)
                require(result["returncode"]!=0,name+": corruption survived")
                require(result["payload"].get("status")=="failed",name+": no failure report")
                require(result["payload"].get("phase")==phase,name+": failed at unexpected phase")
                require(diagnostic in result["payload"].get("error",""),name+": missed intended guard")
                outcomes.append(result)
            records.append({"name":name,"kind":kind,"change":change,"expected_phase":phase,
                            "expected_diagnostic":diagnostic,"normal_and_optimized_detected":True,
                            "results":outcomes})
        for name,path,mutation,phase,diagnostic in data_mutations:
            damaged=deepcopy(base)
            before=pointer_get(damaged,path)
            after=mutation(before)
            pointer_set(damaged,path,after)
            fixture=temp/(name+".json")
            fixture.write_text(json.dumps(damaged,indent=2)+"\n",encoding="utf-8")
            test(name,"independent_fixture_mutation",VERIFIER,fixture,phase,diagnostic,
                 {"json_path":path,"before":before,"after":after})
        for name,before,after,phase,diagnostic in source_mutations:
            require(source.count(before)==1,name+": source mutation anchor not unique")
            script=temp/(name+".py")
            script.write_text(source.replace(before,after,1),encoding="utf-8")
            test(name,"independent_equation_source_mutation",script,FIXTURES,phase,diagnostic,
                 {"before":before,"after":after})
        malformed=[
            ("missing_case",lambda:json.dumps({**base,"frozen_cases":base["frozen_cases"][:-1]}),"complete frozen cases"),
            ("duplicate_key",lambda:original_fixture.decode().replace('"schema":','"schema":"duplicate", "schema":',1),"duplicate JSON key"),
            ("noninteger_json_number",lambda:original_fixture.decode().replace('"M": 1','"M": 1.0',1),"noninteger JSON number forbidden"),
            ("noncanonical_rational",lambda:original_fixture.decode().replace('"v": "5"','"v": "10/2"',1),"noncanonical rational"),
        ]
        for name,make,diagnostic in malformed:
            fixture=temp/(name+".json")
            fixture.write_text(make(),encoding="utf-8")
            # Canonical rational validation happens as exact algebra is loaded.
            phase="frozen_exact_algebra" if name=="noncanonical_rational" else "preflight"
            test(name,"independent_schema_mutation",VERIFIER,fixture,phase,diagnostic,
                 {"operation":name})
    require(FIXTURES.read_bytes()==original_fixture,"committed fixtures changed during campaign")
    require(VERIFIER.read_bytes()==original_source,"committed verifier changed during campaign")
    final=[]
    for opt in (0,1):
        result=execute(VERIFIER,FIXTURES,opt,"final_baseline")
        require(result["returncode"]==0,"post-campaign baseline failed")
        final.append(result)
    result={"schema":"report107-corruption-campaign-v1","status":"passed",
            "scope":"Finite exact regression checks and mutation detection; not analytic proof.",
            "fixture_sha256":sha256(original_fixture).hexdigest(),
            "verifier_sha256":sha256(original_source).hexdigest(),
            "no_assertion_correctness_gates":True,
            "independent_mutations":len(records),"failed_corrupt_runs":2*len(records),
            "baseline_successful_runs":len(baseline)+len(final),
            "baseline":baseline,"mutations":records,"post_campaign_baseline":final}
    (HERE/"corruption_results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in ("status","independent_mutations","failed_corrupt_runs","baseline_successful_runs","no_assertion_correctness_gates")},sort_keys=True))
    return 0


if __name__=="__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print(json.dumps({"status":"failed","error_type":type(error).__name__,"error":str(error)},sort_keys=True),file=sys.stderr)
        sys.exit(1)
