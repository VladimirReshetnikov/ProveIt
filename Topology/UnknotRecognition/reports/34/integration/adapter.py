"""Opt-in callback adapter; no dependency on a guessed fastunknot API.

The caller must supply a checked source braid and a complete/safe backend.
The backend receives a factor Braid and the remaining global time allowance,
and returns a dict with status UNKNOT, KNOTTED, or UNKNOWN.  Unknown can never
be turned into an unknot verdict.  The adapter is tested with stand-ins, not
against an installed upstream package in this environment.
"""
from time import monotonic
from braidkernel import Braid, kernelize
from braidkernel.descent import linear_descent, verify_descent


def recognize_with_backend(strands, word, decide, *, seconds=None, descend=False):
    start=monotonic()
    original=Braid.checked(strands,word)
    source=original
    descent=None
    if descend:
        source,descent=linear_descent(original)
        verify_descent(original,descent)
    result=kernelize(source)
    result['original_braid_dimensions']={'strands':original.strands,'letters':len(original.word)}
    if descent is not None:result['descent_certificate']=descent
    if result['status']!='CORE':return result
    unknown=False
    memo={}
    reports=[]
    for item in result['factors']:
        factor=Braid.checked(item['strands'],item['word'])
        remaining=None if seconds is None else seconds-(monotonic()-start)
        if remaining is not None and remaining<=0:
            result.update(status='UNKNOWN',method='shared-time-budget',backend_reports=reports)
            return result
        key=(factor.strands,factor.word)
        if key not in memo:
            record=decide(factor,remaining)
            if not isinstance(record,dict) or record.get('status') not in {'UNKNOT','KNOTTED','UNKNOWN'}:
                raise ValueError('backend violated the status contract')
            memo[key]=record
        record=memo[key]
        reports.append({'factor':factor.to_json(),'result':record})
        if record['status']=='KNOTTED':
            result.update(status='KNOTTED',method='certified-factor-backend',backend_reports=reports)
            return result
        unknown |= record['status']=='UNKNOWN'
    result.update(status='UNKNOWN' if unknown else 'UNKNOT',
                  method='factor-backend-aggregate',backend_reports=reports)
    return result
