#!/usr/bin/env python3
"""Exploratory quadrature of the real-index Gregory signed integral.

Requires mpmath. Higher-order rows are NOT interval certificates, and a
numerically found continuous zero is not by itself a proof of Gr(m).
Two quadrature orders are compared as a numerical consistency check.
"""
from __future__ import annotations
import argparse
import csv
from math import comb
from pathlib import Path
import mpmath as mp


def quadrature_data(m: int, nodes: int) -> list[tuple]:
    x, weights = mp.gauss_quadrature(nodes, "legendre")
    result = []
    for interval in range(m):
        for xi, wi in zip(x, weights):
            t = interval + (xi+1)/2
            u = min(t, m-t)  # Symmetry reduces density cancellation.
            density = mp.fsum((-1)**j * comb(m,j) * (u-j)**(m-1)
                              for j in range(int(mp.floor(u))+1)) / mp.factorial(m-1)
            q = mp.gamma(t+1)*mp.sin(mp.pi*t)/mp.pi
            result.append((t, wi*density*q/2))
    return result


def normalized_integral(m: int, c, data: list[tuple]):
    L = m+c
    n = mp.exp(L)
    if n <= m:
        raise ValueError("Real-index integral requires exp(m+c) > m")
    offset = -mp.loggamma(n+1) + L + m*mp.log(L)
    return mp.fsum(weight*mp.exp(mp.loggamma(n-t)+offset) for t,weight in data)


def find_zero(m: int, nodes: int, digits: int):
    data = quadrature_data(m,nodes)
    guess = 1-mp.euler-(mp.zeta(2)+mp.zeta(3))/m
    c = mp.findroot(lambda c: normalized_integral(m,c,data),
                    (guess-mp.mpf("0.3"),guess+mp.mpf("0.3")),
                    solver="secant",tol=mp.mpf(10)**(-digits-3))
    return c, data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders",default="3,4,5,6,7,8,9,10,12,16,20,30,50")
    parser.add_argument("--nodes",type=int,default=64)
    parser.add_argument("--check-nodes",type=int,default=96)
    parser.add_argument("--digits",type=int,default=30)
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"data"/"numerical_roots.csv")
    args = parser.parse_args()
    orders = [int(x) for x in args.orders.split(",")]
    if min(orders) < 3 or min(args.nodes,args.check_nodes) < 8 or args.digits < 15:
        parser.error("Require orders >= 3, quadrature nodes >= 8, digits >= 15")
    rows = []
    print("EXPLORATORY: quadrature comparison is not interval certification.",flush=True)
    for m in orders:
        # logGamma(n-t)-logGamma(n+1) loses roughly log10(n) digits.
        mp.mp.dps = args.digits+30+int(mp.ceil(m/mp.log(10)))
        c, _ = find_zero(m,args.nodes,args.digits)
        checked, data = find_zero(m,args.check_nodes,args.digits)
        discrepancy = abs(c-checked)
        if discrepancy > mp.mpf(10)**(-args.digits+6):
            raise ArithmeticError(f"Quadrature disagreement at m={m}: {discrepancy}")
        delta = mp.mpf("1e-12")
        assert normalized_integral(m,checked-delta,data) < 0
        assert normalized_integral(m,checked+delta,data) > 0
        n = mp.exp(m+checked)
        d = 1-mp.euler
        c1 = -mp.zeta(2)-mp.zeta(3)
        c2 = (mp.zeta(2)*mp.zeta(3)+mp.zeta(2)-mp.zeta(3)
              -mp.mpf(5)/2*mp.zeta(4)-3*mp.zeta(5))
        fmt = lambda value: mp.nstr(value,args.digits)
        row = {"m":m,"c_log_zero_minus_m":fmt(checked),"continuous_zero":fmt(n),
               "ceiling_candidate_not_certified":str(int(mp.ceil(n))),
               "zero_over_3_power_m":fmt(n/3**m),"zero_over_e_power_m":fmt(mp.exp(checked)),
               "second_order_c_approximation":fmt(d+c1/m+c2/m**2),
               "quadrature_c_discrepancy":fmt(discrepancy),
               "primary_nodes":args.nodes,"check_nodes":args.check_nodes,
               "working_decimal_precision":mp.mp.dps}
        rows.append(row)
        print(f"m={m:2d}: c={mp.nstr(checked,18)}, "
              f"zero={mp.nstr(n,18)}, node discrepancy={mp.nstr(discrepancy,4)}",flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open("w",newline="",encoding="utf-8") as output:
        writer = csv.DictWriter(output,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
