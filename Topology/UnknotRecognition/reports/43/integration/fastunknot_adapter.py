"""Opt-in adapter for the audited fastunknot interfaces.

Requires the maintained repository on PYTHONPATH, plus this package's src/.
No production files or defaults are changed. This adapter has been source-
audited, but has NOT been run against a complete upstream checkout here.
"""
from time import monotonic
from math import isfinite
from whitehead_exposure.engine import search_presentation


def group_exposure_decide(diagram, *, seconds=1.0, max_letters=200000,
                          max_work=10000000, check=lambda: None):
    from fastunknot.diagram import Diagram
    from fastunknot.group_certificate import _presentation, _Budget, GroupLimit, verify_group_certificate
    if seconds is not None and (type(seconds) not in (int,float) or not isfinite(seconds) or seconds<0):
        raise ValueError('seconds must be finite and nonnegative, or None')
    if type(max_letters) is not int or max_letters<0 or type(max_work) is not int or max_work<0:
        raise ValueError('resource caps must be nonnegative integers')
    start=monotonic();expires=None if seconds is None else start+seconds
    def tick():
        check()
        if expires is not None and monotonic()>=expires:
            raise GroupLimit('exposure local time allowance exhausted')
    # The bare Diagram constructor itself does not validate. Revalidate PD.
    valid=Diagram.from_pd(diagram.pd)
    try:
        tick()
        budget=_Budget(tick,max_letters,max_work)
        alive,words=_presentation(valid,budget)
        result=search_presentation(words,alive,max_letters=max_letters,
                                  max_work=max(0,budget.left),check=tick)
        tick()
        if result['status']!='FREE_RANK_ONE':
            return {'status':'INCONCLUSIVE','reason':result['reason'],'seconds':monotonic()-start,
                    'exposure_result':result}
        certificate={'version':1,'method':'wirtinger-cyclic-group','status':'UNKNOT',
                     'input_pd':[list(row) for row in valid.pd], 'moves':result['moves'],
                     'remaining_generator':result['remaining_generator']}
        # Reuse the maintained verifier: it already permits positive-length
        # Whitehead moves. A 3M workspace permits one exposure before elimination.
        if not verify_group_certificate(valid,certificate,check=tick,
                                         max_letters=3*max_letters,max_work=max_work):
            raise ArithmeticError('upstream independent replay rejected exposure trace')
        tick()
        return {'status':'UNKNOT','certificate':certificate,'seconds':monotonic()-start,
                'exposure_result':result}
    except GroupLimit as exc:
        check()
        return {'status':'INCONCLUSIVE','reason':str(exc),'seconds':monotonic()-start}
