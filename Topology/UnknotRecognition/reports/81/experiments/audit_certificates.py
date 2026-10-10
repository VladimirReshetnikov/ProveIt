"""Focused adversarial certificate and public-budget audit."""
from copy import deepcopy
from pathlib import Path
from fractions import Fraction
from math import gcd
import argparse
import hashlib
import json
import sys

PACKAGE = Path(__file__).resolve().parents[1]


def run(args):
    fast = args.fast.resolve()
    sys.path.insert(0, str(fast))
    sys.path.insert(0, str(fast / 'tests'))
    from test_normal_sector_integration import solid_torus, capped_solid_torus
    from fastunknot.sector_planar import enumerate_planar_sector
    from fastunknot.sector_planar_certificate import certify_planar_sector, discover_planar_in_sector
    from fastunknot.sector_planar_verify import (
        verify_planar_sector_certificate, verify_planar_exhaustion,
        PlanarVerificationLimit,
    )
    from fastunknot.normal_sector import SearchLimit
    from fastunknot.normal_sector_verify import dense_sector_model, _lift

    checks=[]
    def ensure(condition,label):
        if not condition:
            raise AssertionError(label)
        checks.append(label)

    def rejected(tri, cert, name, verifier=verify_planar_sector_certificate):
        ensure(verifier(tri,cert) is False,name)

    class Counter:
        def __init__(self): self.calls=0
        def __call__(self): self.calls+=1
    class Cancelled(RuntimeError): pass
    class FalseyCancel:
        def __init__(self,at): self.calls=0; self.at=at
        def __bool__(self): return False
        def __call__(self):
            self.calls+=1
            if self.calls==self.at: raise Cancelled('audit cancellation')

    tri=capped_solid_torus()
    support=[(0,2),(1,0)]
    answer=certify_planar_sector(tri,support)
    certificate=answer['certificate']
    ensure(answer['status']=='COMPLETE','baseline complete')
    ensure(verify_planar_sector_certificate(tri,certificate),'baseline independent replay')
    model=dense_sector_model(tri,support)
    directions={tuple(row[t][4+q] for t,q in support):row for row in answer['coordinates']}
    for q in certificate['quadrilateral_rays']:
        rows=directions[tuple(q)]
        ensure(rows==_lift(model,q,lambda:None),'projected integer lift equals dense lift '+str(q))
        common=0
        for row in rows:
            for x in row:
                ensure(type(x) is int and x>=0,'integral nonnegative coordinate')
                common=gcd(common,x)
        ensure(common==1,'full standard lift primitive')

    for name,mutator in [
        ('schema',lambda c:c.update(schema='normal-sector-planar-rays-v0')),
        ('source digest',lambda c:c.update(source_sha256='0'*64)),
        ('missing ray',lambda c:c['quadrilateral_rays'].pop()),
        ('duplicate ray',lambda c:c['quadrilateral_rays'].append(c['quadrilateral_rays'][0])),
        ('ray order',lambda c:c['quadrilateral_rays'].reverse()),
        ('nonprimitive ray',lambda c:c['quadrilateral_rays'].__setitem__(0,[2*x for x in c['quadrilateral_rays'][0]])),
        ('negative ray',lambda c:c['quadrilateral_rays'][0].__setitem__(0,-1)),
        ('boolean coordinate',lambda c:c['quadrilateral_rays'][0].__setitem__(0,True)),
        ('float coordinate',lambda c:c['quadrilateral_rays'][0].__setitem__(0,0.0)),
        ('rational object coordinate',lambda c:c['quadrilateral_rays'][0].__setitem__(0,Fraction(1))),
        ('coordinate width',lambda c:c['quadrilateral_rays'][0].append(0)),
        ('nonlist row',lambda c:c['quadrilateral_rays'].__setitem__(0,tuple(c['quadrilateral_rays'][0]))),
        ('support order',lambda c:c['allowed_types'].reverse()),
        ('overlapping support',lambda c:c['allowed_types'].__setitem__(1,[0,1])),
        ('out of range support',lambda c:c['allowed_types'].__setitem__(1,[9,0])),
        ('boolean support',lambda c:c['allowed_types'][0].__setitem__(0,False)),
    ]:
        altered=deepcopy(certificate); mutator(altered)
        rejected(tri,altered,'reject '+name)
    source=deepcopy(tri); source['audit_added_metadata']=True
    rejected(source,certificate,'source binding includes metadata')
    source=solid_torus()
    rejected(source,certificate,'source binding rejects another triangulation')
    for malformed in [None,[],False,1,'',{}]:
        rejected(tri,malformed,'reject malformed '+repr(malformed))

    # Complete enumeration and partial production cannot be confused.
    budget_checks=[]
    for fn in [certify_planar_sector,discover_planar_in_sector]:
        callback=Counter()
        limited=fn(tri,[(1,0)],max_work=0,check=callback)
        ensure(limited['status']=='INCONCLUSIVE' and 'certificate' not in limited,
               fn.__name__+' budget zero has no certificate')
        ensure(callback.calls==1,fn.__name__+' budget includes kernel')
        budget_checks.append(dict(api=fn.__name__,max_work=0,calls=callback.calls,
                                  status=limited['status']))
    baseline=certify_planar_sector(tri,support)
    total=baseline['stats']['work_units']
    for cap in sorted({1,total//2,total-1,total}):
        got=certify_planar_sector(tri,support,max_work=cap)
        ensure(got['status']==('COMPLETE' if cap==total else 'INCONCLUSIVE'),
               'exact public budget '+str(cap))
        ensure(got['stats']['work_units']<=cap,'work never overshoots')
        ensure(('certificate' in got)==(cap==total),'budget certificate presence')
        budget_checks.append(dict(api='certify_planar_sector',max_work=cap,
                                 work_units=got['stats']['work_units'],status=got['status']))
    for bad in [True,1.0,-1,'1']:
        try: certify_planar_sector(tri,support,max_work=bad)
        except ValueError: checks.append('reject malformed max_work '+repr(bad))
        else: raise AssertionError('invalid max_work accepted')

    # False-valued callbacks remain active, and unrelated cancellation propagates.
    for fn in [certify_planar_sector,discover_planar_in_sector]:
        for stop in [1,4,10]:
            try: fn(tri,support,check=FalseyCancel(stop))
            except Cancelled: checks.append(fn.__name__+' cancellation '+str(stop))
            else: raise AssertionError('cancellation swallowed')
    for stop in [1,4,10]:
        try: verify_planar_sector_certificate(tri,certificate,check=FalseyCancel(stop))
        except Cancelled: checks.append('independent verifier cancellation '+str(stop))
        else: raise AssertionError('verifier cancellation swallowed')
    try: verify_planar_sector_certificate(tri,certificate,max_work=0)
    except PlanarVerificationLimit: checks.append('independent geometry limit propagates')
    else: raise AssertionError('verification limit swallowed')

    # Negative topology records must be bound to the full list and correct replay.
    negative=discover_planar_in_sector(tri,[(1,0)])
    ensure(negative['status']=='NO_VERTEX_DISC_IN_SECTOR','negative fixture restricted status')
    proof=negative['certificate']
    ensure(verify_planar_exhaustion(tri,proof),'negative baseline replay')
    for name,mutator in [
        ('negative status',lambda c:c.update(status='NO_POSITIVE_EULER')),
        ('missing topology ray',lambda c:c['rays'].clear()),
        ('false Euler',lambda c:c['rays'][0].update(euler_characteristic=0)),
        ('boolean Euler',lambda c:c['rays'][0].update(euler_characteristic=True)),
        ('missing disk replay',lambda c:c['rays'][0].pop('disk_certificate')),
        ('false disk count',lambda c:c['rays'][0]['disk_certificate'].update(compressing_disk_components=1)),
    ]:
        changed=deepcopy(proof); mutator(changed)
        rejected(tri,changed,'reject '+name,verify_planar_exhaustion)

    summary=dict(status='PASS',assertions=len(checks),checks=checks,budget_checks=budget_checks,
                 source_sha256={name:hashlib.sha256((fast/'fastunknot'/name).read_bytes()).hexdigest()
                                for name in ['sector_planar.py','sector_planar_verify.py',
                                             'sector_planar_certificate.py']})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='checks'},indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, default=PACKAGE / 'code',
                        help='Directory containing fastunknot and tests (default: bundled code)')
    parser.add_argument('--output', type=Path,
                        default=PACKAGE / 'results' / 'certificate_audit.json',
                        help='Destination for the complete JSON audit record')
    run(parser.parse_args())


if __name__ == '__main__':
    main()
