#!/usr/bin/env python3
"""Compile two certified same-base Pell pools into one reciprocal pool.

No third-party modules are required. The arithmetic theorem is in the report;
this file constructs the finite polynomial, not a proof of that theorem.
The input must retain the four original labelled pool rows and private K,L.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path


def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(x):
    return hashlib.sha256(canonical(x)).hexdigest()


def load_poly(terms, n):
    result = {}
    for c, m in terms:
        if type(c) is not int or not c or any(type(i) is not int or not 0 <= i < n for i in m):
            raise ValueError("Invalid coefficient or coordinate")
        mon = tuple(sorted(m))
        if mon in result:
            raise ValueError("Duplicate monomial")
        result[mon] = c
    return result


def serial(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]


def add(p, q, scalar=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + scalar*c
        if not r[m]:
            del r[m]
    return r


def mul(p, q):
    r = {}
    for m, c in p.items():
        for k, d in q.items():
            z = tuple(sorted(m+k))
            r[z] = r.get(z, 0) + c*d
    return {m:c for m,c in r.items() if c}


def scale(p, c):
    return {m:c*d for m,d in p.items() if c*d}


def coefficient(p, coordinate):
    """Coefficient of a coordinate which occurs with degree at most one."""
    result = {}
    for m,c in p.items():
        count = m.count(coordinate)
        if count > 1:
            raise ValueError("Private pool coordinate is not linear")
        if count:
            reduced = list(m)
            reduced.remove(coordinate)
            key = tuple(reduced)
            result[key] = result.get(key,0)+c
    return {m:c for m,c in result.items() if c}


def restrict(p, coordinates):
    return {m:c for m,c in p.items() if not set(m).intersection(coordinates)}


def compile_reciprocal(parent):
    if parent.get("domain") != "unrestricted integers":
        raise ValueError("The theorem requires unrestricted integer coordinates")
    n = len(parent["variables"])
    names = [v["name"] for v in parent["variables"]]
    labels = [r["label"] for r in parent["residuals"]]
    rows = [load_poly(r["terms"], n) for r in parent["residuals"]]
    groups = []
    removed_vars, removed_rows = set(), set()
    for group in ("radix", "radix_plus_one"):
        K = names.index(group+".K")
        L = names.index(group+".L")
        ia = labels.index(group+".bilinear_aggregate")
        ib = labels.index(group+".pooled_norm")
        ar, br = rows[ia], rows[ib]
        if coefficient(ar,K) != {():1} or coefficient(br,L) != {():1}:
            raise ValueError("Pool rows have unexpected unit coefficients")
        base = scale(coefficient(br,K), -1)
        a = coefficient(ar,L)
        if any(len(m)>1 for m in base) or any(len(m)>1 for m in a):
            raise ValueError("Base or modulus factor is not affine")
        ar0, br0 = restrict(ar,{K,L}), restrict(br,{K,L})
        if ar != add(add({(K,):1},mul(a,{(L,):1})),ar0):
            raise ValueError("Unexpected private-coordinate interaction")
        if br != add(add(br0,scale(mul(base,{(K,):1}),-1)),{(L,):1}):
            raise ValueError("Unexpected norm row")
        E = add(br0,mul(base,ar0))
        T = add({():-1},mul(base,a),-1)
        # Verify the exact elimination identity E-T*L = br+base*ar.
        if add(E,mul(T,{(L,):1}),-1) != add(br,mul(base,ar)):
            raise ValueError("Pool elimination identity failed")
        groups.append({"group":group,"K":K,"L":L,"aggregate_row":ia,
                       "norm_row":ib,"base":serial(base),"a":serial(a),
                       "E":serial(E),"T":serial(T)})
        removed_vars.update((K,L))
        removed_rows.update((ia,ib))
    if len(removed_vars)!=4 or len(removed_rows)!=4:
        raise ValueError("Overlapping private pools")
    for j,row in enumerate(rows):
        if j not in removed_rows and any(set(m)&removed_vars for m in row):
            raise ValueError("Removed coordinate is not private")
    for group in groups:
        other = removed_vars-{group["K"],group["L"]}
        if any(set(m)&other for j in (group["aggregate_row"],group["norm_row"]) for m in rows[j]):
            raise ValueError("Pool coordinates interact")
    b0=load_poly(groups[0]["base"],n);b1=load_poly(groups[1]["base"],n)
    if add(b1,b0,-1)!={():1}:
        raise ValueError("The bases are not consecutive in the required order")
    # The two rows must use the same Pell parameter 2A=base-a.
    twoA0=add(b0,load_poly(groups[0]["a"],n),-1)
    twoA1=add(b1,load_poly(groups[1]["a"],n),-1)
    if twoA0 != twoA1:
        raise ValueError("Different Pell parameters")
    E0,E1=[load_poly(g["E"],n) for g in groups]
    T0,T1=[load_poly(g["T"],n) for g in groups]
    rp=add(add(mul(E0,T1),mul(E1,T0)),mul({(n,):1},mul(T0,T1)),-1)
    retained=[j for j in range(n) if j not in removed_vars]
    rename={j:k for k,j in enumerate(retained)}
    rename[n]=len(retained)
    def remap(p):
        return {tuple(rename[j] for j in m):c for m,c in p.items()}
    out={"schema":"conzfc-reciprocal-pooling-v1","domain":"unrestricted integers",
         "polynomial":"sum(square(row) for row in residuals)",
         "variant":f"reciprocal_pooling_{n-3}","parent_equation_sha256":sha(parent),
         "variables":[copy.deepcopy(parent["variables"][j]) for j in retained]
                     +[{"kind":"reciprocal_pool","name":"reciprocal.z"}],
         "residuals":[{"label":parent["residuals"][j]["label"],"terms":serial(remap(row))}
                      for j,row in enumerate(rows) if j not in removed_rows]
                     +[{"label":"reciprocal.consecutive_bases","terms":serial(remap(rp))}]}
    certificate={"schema":"reciprocal-pooling-certificate-v1","groups":groups,
                 "input_sha256":sha(parent),"output_sha256":sha(out),
                 "removed_variables":sorted(removed_vars),"removed_rows":sorted(removed_rows),
                 "retained_old_indices":retained,"two_A_original":serial(twoA0),
                 "new_variable_original_index":n,
                 "new_residual_original_indices":serial(rp),
                 "forward_quotient":"z=L_radix+L_radix_plus_one",
                 "inverse_quotients":"L_j=E_j/T_j; K_j=-a_j*L_j-aggregate_row_j(K=L=0)",
                 "scope":"Exact row identities plus the proved reciprocal-pooling theorem; not a global polynomial automorphism."}
    return out,certificate


def expanded(equation):
    n=len(equation["variables"])
    result={}
    for row in equation["residuals"]:
        p=load_poly(row["terms"],n)
        result=add(result,mul(p,p))
    return result


def metrics(equation,p):
    rows=[load_poly(r["terms"],len(equation["variables"])) for r in equation["residuals"]]
    return {"variables":len(equation["variables"]),"residuals":len(rows),
            "degree":max(map(len,p),default=0),"collected_terms":len(p),
            "coefficient_height":max(map(abs,p.values()),default=0),
            "maximum_residual_degree":max(len(m) for row in rows for m in row),
            "residual_terms":sum(len(row) for row in rows),
            "residual_height":max(abs(c) for row in rows for c in row.values()),
            "all_coordinates_used":set(i for m in p for i in m)==set(range(len(equation["variables"])))}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input",type=Path)
    ap.add_argument("output",type=Path)
    args=ap.parse_args()
    equation,certificate=compile_reciprocal(json.loads(args.input.read_text()))
    p=expanded(equation)
    met=metrics(equation,p)
    args.output.mkdir(parents=True,exist_ok=True)
    for name,data in (("equation.json",equation),("certificate.json",certificate),
                      ("METRICS.json",met),("expanded_polynomial.json",{"schema":"sparse-polynomial-v1","terms":serial(p)})):
        (args.output/name).write_bytes(canonical(data))
    print(json.dumps(met,sort_keys=True))


if __name__=="__main__":
    main()
