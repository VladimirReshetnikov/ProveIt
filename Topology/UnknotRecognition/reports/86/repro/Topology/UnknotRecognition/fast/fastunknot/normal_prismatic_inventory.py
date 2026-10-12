"""Source-bound binary normal midsection inventory for wholly prismatic cuts.

Core components are only counted. Each returned base is a connected normal
midsection of an interval bundle, which can be twisted; multiplicities remain
binary. No full core geometry, attachments or knot verdict is produced.
"""
from .normal_cut_complement import _chamber_system,_exceptional_chambers
from .normal_surface_geometry import _prepare,_coordinates,_fingerprint
from .weighted_orbits import weighted_orbit_histogram,weighted_histogram_from_orbit_certificate


def _prism_weights(rows,check):
    dimension=1+7*len(rows);weights=[];offset=0
    def unit(column):
        value=[0]*dimension;value[column]=1;return value
    for point in _exceptional_chambers(rows,check):
        check();weights.append((point,point+1,unit(0)))
    for t,row in enumerate(rows):
        check();q=sum(row[4:]);typ=next((j for j in range(3)if row[4+j]),None)
        if q>1:weights.append((offset+1,offset+q,unit(1+7*t+4+typ)))
        offset+=q+1
        for v,count in enumerate(row[:4]):
            check()
            if count>1:weights.append((offset+1,offset+count,unit(1+7*t+v)))
            offset+=count
    return dimension,weights


def _inventory(prepared,rows,histogram,check):
    core=prismatic=0;bases=[];t=len(rows)
    for item in histogram:
        check();weight=item['weight'];copies=item['orbits']
        if weight[0]>0:core+=copies;continue
        vector=[list(weight[1+7*i:1+7*(i+1)])for i in range(t)]
        if not any(x for row in vector for x in row):raise ArithmeticError('empty prism midsection')
        analysed=_coordinates(prepared,vector,check)
        if any(x>bound for row,source in zip(vector,rows)for x,bound in zip(row,source)):
            raise ArithmeticError('midsection exceeds cutting vector')
        prismatic+=copies
        bases.append(dict(coordinates=vector,multiplicity=copies,euler_characteristic=analysed['euler_characteristic']))
    if not 1<=core<=6*t:raise ArithmeticError('invalid conservative core count')
    q=sum(any(row[4:])for row in rows)
    if len(bases)>prepared['vertices']+2*q:raise ArithmeticError('normal midsection type bound failed')
    return dict(core_components=core,prismatic_components=prismatic,bases=bases)


def normal_prismatic_inventory(triangulation,coordinates,*,max_cycles=None,
        orbit_certificate=None,record_certificate=False,periodic_rule='fine_wilf',check=lambda:None):
    """Recover normal midsections and multiplicities without chamber expansion.

    The existing finite orientable one-torus source contract applies. A supplied
    orbit trace is independently checked against fresh geometric pairings;
    max_cycles must then be None. Cycle caps govern orbit search, not weighted
    replay; callbacks apply throughout. Incomplete work emits no inventory.
    Coordinates are not divided by their gcd: an annular midsection can be the
    connected double of a one-sided normal vector.
    """
    check()
    if type(record_certificate)is not bool:raise ValueError('record_certificate must be bool')
    if max_cycles is not None and(type(max_cycles)is not int or max_cycles<0):raise ValueError('max_cycles must be nonnegative or None')
    if orbit_certificate is not None and max_cycles is not None:raise ValueError('max_cycles cannot constrain supplied trace replay')
    if periodic_rule not in ('fine_wilf','aht'):raise ValueError('unknown periodic rule')
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    size,pairs=_chamber_system(prepared,analysed['rows'],check)
    dimension,weights=_prism_weights(analysed['rows'],check)
    if orbit_certificate is None:
        query=weighted_orbit_histogram(size,pairs,weights,dimension=dimension,max_cycles=max_cycles,
            periodic_rule=periodic_rule,check=check,record_certificate=record_certificate)
    else:
        query=weighted_histogram_from_orbit_certificate(size,pairs,weights,orbit_certificate,
            dimension=dimension,check=check,record_certificate=record_certificate)
    result=dict(status=query['status'],tetrahedra=len(analysed['rows']),chamber_points=size,
        interval_pairings=len(pairs),weight_dimension=dimension,stats=query['stats'],
        trust='normal midsections of wholly prismatic cut components on the supplied source; no knot verdict')
    if query['status']!='COMPLETE':return result
    inventory=_inventory(prepared,analysed['rows'],query['histogram'],check)
    result['inventory']=inventory;result['cut_components']=query['orbit_count']
    if query['orbit_count']!=inventory['core_components']+inventory['prismatic_components']:
        raise ArithmeticError('inventory component total disagrees')
    if record_certificate:
        result['certificate']=dict(schema='normal-prismatic-inventory-v1',
            input_sha256=_fingerprint(triangulation,analysed,check),inventory=inventory,
            weighted_certificate=query['certificate'])
    check();return result
