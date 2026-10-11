"""Independent chamber-weight construction and normal midsection inventory replay."""
from .normal_cut_complement_verify import _reference_chambers
from .normal_surface_geometry import _prepare,_coordinates,_fingerprint
from .integer_codec import encoded_integer,certificate_equal
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _reference_prism_weights(rows,check):
    dimension=7*len(rows)+1;offset=0;intervals=[]
    for t,row in enumerate(rows):
        check();q=sum(row[4:]);typ=next((j for j in range(3)if row[4+j]),None)
        blocks=[(offset,offset+q+1,None if typ is None else 4+typ,True)]
        offset+=q+1
        for v,count in enumerate(row[:4]):
            blocks.append((offset,offset+count,v,False));offset+=count
        for lo,stop,column,chain in blocks:
            check()
            if lo==stop:continue
            marks=[lo]
            if chain and stop-lo>1:marks.append(stop-1)
            for p in marks:
                value=[0]*dimension;value[0]=1;intervals.append((p,p+1,value))
            low=lo+1;high=stop-1 if chain else stop
            if low<high:
                value=[0]*dimension;value[1+7*t+column]=1;intervals.append((low,high,value))
    return dimension,intervals


def verify_normal_prismatic_inventory(triangulation,coordinates,certificate,*,max_operations=None,check=lambda:None):
    """Verify weighted source ownership and every base vector and multiplicity.

    Invalid source geometry raises the established NormalOrbitError. Bad proofs
    return False; callback exceptions propagate. Operation limits count the
    supplied ordinary orbit trace, and do not imply a geometric conclusion.
    """
    check()
    if max_operations is not None and(type(max_operations)is not int or max_operations<0):raise ValueError('invalid max_operations')
    if(type(certificate)is not dict or set(certificate)!={'schema','input_sha256','inventory','weighted_certificate'}
            or certificate.get('schema')!='normal-prismatic-inventory-v1'):return False
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    if certificate['input_sha256']!=_fingerprint(triangulation,analysed,check):return False
    proof=certificate['weighted_certificate']
    if type(proof)is not dict or type(proof.get('orbit_proof'))is not dict:return False
    trace=proof['orbit_proof']
    if type(trace.get('operations'))is not list:return False
    if max_operations is not None and len(trace['operations'])>max_operations:return False
    size,pairs=_reference_chambers(prepared,analysed['rows'],check)
    dimension,weights=_reference_prism_weights(analysed['rows'],check)
    if not verify_weighted_orbit_certificate(size,pairs,weights,proof,dimension=dimension,check=check):return False
    core=prismatic=0;bases=[];t=len(analysed['rows'])
    for row in proof['histogram']:
        check();weight=[encoded_integer(x)for x in row['weight']];copies=encoded_integer(row['orbits'])
        if weight[0]>0:core+=copies;continue
        vector=[weight[1+7*i:1+7*(i+1)]for i in range(t)]
        if not any(any(r)for r in vector):return False
        local=_coordinates(prepared,vector,check)
        if any(a>b for r,s in zip(vector,analysed['rows'])for a,b in zip(r,s)):return False
        prismatic+=copies;bases.append(dict(coordinates=vector,multiplicity=copies,euler_characteristic=local['euler_characteristic']))
    if not 1<=core<=6*t:return False
    if len(bases)>prepared['vertices']+2*sum(any(row[4:])for row in analysed['rows']):return False
    expected=dict(core_components=core,prismatic_components=prismatic,bases=bases)
    return certificate_equal(certificate['inventory'],expected)
