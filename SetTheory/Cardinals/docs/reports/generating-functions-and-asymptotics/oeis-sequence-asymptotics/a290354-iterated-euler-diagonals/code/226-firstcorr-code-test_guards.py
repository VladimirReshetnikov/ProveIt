#!/usr/bin/env python3
"""Optimization-safe public input-guard tests; standard library by default.

--with-diagnostics additionally checks NumPy/SciPy diagnostic input guards and
requires those packages. Exact arithmetic here validates all supported formal
coordinate orders 0..12; it does not prove an analytic remainder estimate.
"""
import argparse
import json
import sys
from exact_euler import bounded_index,decimal,euler_step,product_step,coefficients,diagonal
from coordinate_series import generate,KNOWN


def run(with_diagnostics=False):
    checks = 0

    def equal(actual,expected,label):
        nonlocal checks
        if actual!=expected:
            raise ArithmeticError('check failed: '+label)
        checks += 1

    def rejects(function,label):
        nonlocal checks
        try:
            function()
        except ValueError:
            checks += 1
            return
        raise ArithmeticError('guard did not reject: '+label)

    original_limit = sys.get_int_max_str_digits()
    for order in range(13):
        series = generate(order)
        equal(len(series),order,'supported coordinate order '+str(order))
        equal([str(value) for value in series[:9]],KNOWN[:min(order,9)],'known formal coefficients')
    for bad in (-1,13,True,1.5,'9',None):
        rejects(lambda bad=bad:generate(bad),'formal order')
    for bad in (-1,641,True,1.5,'5',None):
        rejects(lambda bad=bad:bounded_index(bad),'index/height')
        rejects(lambda bad=bad:diagonal(bad),'diagonal limit')
        rejects(lambda bad=bad:coefficients(bad,0),'coefficient degree')
        rejects(lambda bad=bad:coefficients(0,bad),'coefficient height')
    for bad in ([],[1],[0,-1],[0,True],[0,1.5],(0,1),None,[0]*642):
        rejects(lambda bad=bad:euler_step(bad),'Euler row')
    rejects(lambda:product_step([0]*22),'product cap')
    for bad in (True,1.5,'1',None):
        rejects(lambda bad=bad:decimal(bad),'decimal input')
    equal(decimal(0),'0','zero serialization')
    equal(decimal(10**3000),'1'+'0'*3000,'large positive serialization')
    equal(decimal(-10**3000),'-1'+'0'*3000,'large negative serialization')
    if with_diagnostics:
        from derivative_diagnostic import validate,comparisons
        for bad in (49,201,True,1.5,'100',None):
            rejects(lambda bad=bad:validate(bad,10,.1),'derivative depth')
        for bad in (9,10001,True,float('inf'),float('nan'),'10',None):
            rejects(lambda bad=bad:validate(100,bad,.1),'derivative cutoff')
        for bad in (.004,.101,True,float('inf'),float('nan'),'.02',None):
            rejects(lambda bad=bad:validate(100,10,bad),'derivative step')
        rejects(lambda:validate(100,10000,.005),'derivative mesh cap')
        for bad in (0,415,True,1.5,'20',None):
            rejects(lambda bad=bad:comparisons({},[bad]),'comparison index')
        equal(validate(50,10,.1),100,'smallest depth and cutoff')
        equal(validate(200,10000,.01),1000000,'largest depth and mesh')
        equal(validate(100,10,.03)%2,0,'even Simpson mesh')
        from amplitude_diagnostic import evaluate
        for bad in (49,201,True,1.5):
            rejects(lambda bad=bad:evaluate(bad,0,10,.1),'inherited amplitude depth')
        for setting in ((100,float('nan'),10,.1),(100,0,float('inf'),.1),
                        (100,0,10,float('nan')),(100,1,10,.1),(100,0,9,.1),
                        (100,0,10,.001),(100,0,10000,.005)):
            rejects(lambda setting=setting:evaluate(*setting),'inherited amplitude numeric limits')
    equal(sys.get_int_max_str_digits(),original_limit,'global integer digit setting unchanged')
    return {'status':'passed','guard_and_finite_order_checks':checks,
            'tested_formal_orders':[0,12],'diagnostic_guards_checked':with_diagnostics,
            'integer_string_limit':original_limit,'optimization':sys.flags.optimize}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-diagnostics',action='store_true')
    args = parser.parse_args()
    print(json.dumps(run(args.with_diagnostics),indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
