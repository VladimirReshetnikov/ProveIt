#!/usr/bin/env python3
"""Exact arithmetic certificates for the degree-sensitive corollaries.

Requires verify_variable_arity.py in the same directory.  These are
normalized contraction bound checks, not measured SAT performance.
"""
from __future__ import annotations
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path
import sys

from verify_variable_arity import (
    A_INF, FS, LOG_UPPER, RS, atan_bounds, coefficient_upper,
    display_coefficient, require, sqrt_upper,
)


def moderate_degree():
    tau = F(4)
    maintained = F(3, 5)
    A, previous = F(), F()
    rows=[]
    for d, (r,f) in enumerate(zip(RS,FS)):
        A += tau*f
        g=LOG_UPPER[r]
        high = maintained+(2 if d==0 else 1)*g*A
        column = maintained+2*g*A if d==0 else 2*g*A+previous
        padding = (1+2*g)*A
        require(max(high,column,padding)<1,f'moderate packing depth {d}')
        rows.append({'depth':d,'high_degree_power':str(high),
                     'column_power':str(column),'padding_power':str(padding)})
        previous=A
    tail_A=tau*A_INF
    high=maintained+2*tail_A
    pure=5*tail_A
    require(tail_A<maintained,'moderate degree invariant')
    require(high<1 and pure<1,'moderate tail packing')
    require(max(F(row['high_degree_power']) for row in rows)==F(6249,6250),
            'moderate maximum high-degree exponent')
    require(pure==F(499,500),'moderate maximum pure-packing exponent')
    lower_sqrt=F(2)
    require(lower_sqrt**2==tau,'incorrect square-root value')
    upper=coefficient_upper()/lower_sqrt
    require(upper<32,'moderate coefficient not below 32')
    with localcontext() as c:
        c.prec=55
        value=Decimal(display_coefficient())/2
    return {'coefficient_decimal':str(value),
            'certified_coefficient_upper':str(upper),
            'certified_coefficient_upper_decimal':float(upper),
            'safe_eventual_coefficient':32,
            'maintained_degree_exponent':str(maintained),
            'created_degree_exponent':str(tail_A),
            'maximum_high_degree_packing_exponent':'6249/6250',
            'maximum_pure_packing_exponent':str(pure),
            'prefix_margins':rows}


def low_degree():
    # log2 48 = 4 + log2 3 < 4 + 8/5.
    require(3**5<2**8,'log2(48) upper bound')
    A=F(4,49)
    g=F(28,5)
    degree=F(1,12)
    high=2*A*g+degree
    padding=(1+2*g)*A
    require(high==F(419,420) and high<1,'low-degree packing exponent')
    require(padding==F(244,245) and padding<1,'low-degree rounding exponent')
    require(degree-A==F(1,588),'low-degree creation margin')
    require(F(1,24)<F(1,12)<F(1,8),'low-degree depth bootstrap')
    upper=F(22,7)/F(693,1000)*sqrt_upper(F(329,12))/(1-sqrt_upper(F(2))/12)
    require(upper<27,'low-degree coefficient not below 27')
    with localcontext() as c:
        c.prec=55
        a5,b5=atan_bounds(F(1,5),50)
        a239,b239=atan_bounds(F(1,239),50)
        p=(16*(a5+b5)-4*(a239+b239))/2
        pi=Decimal(p.numerator)/Decimal(p.denominator)
        value=pi*(Decimal(329)/12).sqrt()/(Decimal(2).ln()*(1-Decimal(2).sqrt()/12))
    return {'coefficient_decimal':str(value),
            'exact_formula':'pi*sqrt(329/12)/(ln(2)*(1-sqrt(2)/12))',
            'certified_coefficient_upper':str(upper),
            'certified_coefficient_upper_decimal':float(upper),
            'safe_eventual_coefficient':27,
            'maintained_degree_exponent':str(degree),
            'created_degree_exponent':str(A),
            'packing_exponent':str(high),
            'rounding_exponent':str(padding)}


def main():
    result={'status':'pass','moderate_degree':moderate_degree(),
            'low_degree':low_degree(),
            'scope':'normalized polynomial-space contraction certificates; same input encoding and oracle hypotheses required for comparison'}
    target=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('degree_corollaries_validation.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
