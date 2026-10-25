"""Authenticate the sum-of-squares frame and coverage of all 14 pooled ports.

Usage: python3 check_frame_coverage.py --equation PATH --receipt PATH
This checker reads no producer code or certificates. It reconstitutes the
literal frame from the actual affine arithmetic ports and compares every
coefficient. It accepts the parent, strict-horizon, and linear-beta variants.
"""
from collections import defaultdict
from pathlib import Path
import argparse,json,hashlib

def add(*args):
    out=defaultdict(int)
    for p in args:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def square(p):
    out=defaultdict(int)
    for m,c in p.items():
        for n,d in p.items():out[tuple(sorted(m+n))]+=c*d
    return dict(out)
def check(path):
    raw=path.read_bytes();eq=json.loads(raw)
    names={v['name']:i for i,v in enumerate(eq['variables'])}
    def port(name,shift=0):
        return add({(names[name],):1},{():shift} if shift else {})
    t=port('t0');f2=port('mul.1');w=port('shared.W')
    explicit=[('horizon',t),('horizon_plus_one',add(t,{():1})),
              ('factorial_base',add(f2,{():1})),
              ('factorial_upper_index',add(t,f2)),
              ('schema_a',port('crt.encoded.a',-1)),
              ('radix',port('pow2.output',-1))]
    simple=['x','y','choose0.output','pow0.output',
            'crt.encoded.b','crt.encoded.c','crt.encoded.d','crt.encoded.S',
            'crt.encoded.Sp','crt.encoded.u','crt.encoded.vq',
            'crt.encoded_index_minus_one','pow1.output','add.380',
            'pow2.output','pow3.output','pow4.output','pow5.output',
            'pow6.output','pow7.output','pow8.output','pow9.output',
            'pow10.output','pow11.output','pow12.output','pow13.output',
            'pow14.output','pow15.output','pow16.output','pow17.output',
            'self_radix.BH']
    for name in simple:
        if name=='pow6.output' and name not in names:continue
        if name=='y' and name not in names:
            # The audited linear-beta change is y+1=V in these coordinates.
            explicit.append(('beta_base_plus_one',port('pow0.output')))
        else:explicit.append((name,port(name)))
    expected=add(w,{():-2},*[scale(-1,square(p)) for _,p in explicit])
    candidates=[r for r in eq['residuals'] if r['label']=='shared.frame_definition']
    if len(candidates)!=1:raise ValueError('unique square-frame definition missing')
    actual={tuple(m):c for c,m in candidates[0]['terms']}
    if actual!=expected:raise ValueError('literal square-frame identity mismatch')
    atoms=[p for _,p in explicit]
    # Every distinct requested base, output and index is checked for literal
    # membership in the just-authenticated sum of affine squares.
    plus_powers=[3,5,7,8,9,10,12,13,15,16,17]
    radix_powers=[4,11,14]
    plus_indices=[add(f2,t),port('crt.encoded.a',-1),
                  *[port('crt.encoded.'+x) for x in ('b','c','d','S','Sp','u','vq')],
                  port('crt.encoded_index_minus_one'),port('add.380')]
    beta=port('y') if 'y' in names else port('pow0.output')
    radix_indices=[t,beta,port('x')]
    ports=[]
    for group,base,powers,indices in [
        ('radix_plus_one',port('pow2.output'),plus_powers,plus_indices),
        ('radix',port('pow2.output',-1),radix_powers,radix_indices)]:
        if len(powers)!=len(indices):raise ValueError('port list mismatch')
        if base not in atoms:raise ValueError('base absent from frame')
        for no,k in zip(powers,indices):
            m=port(f'pow{no}.output')
            if k not in atoms or m not in atoms:raise ValueError(('unbounded port',group,no))
            ports.append({'group':group,'power_request':no,
                          'base_square_covered':True,'index_square_covered':True,
                          'output_square_covered':True})
    return {'status':'PASS','equation_sha256':hashlib.sha256(raw).hexdigest(),
            'frame_identity':'W = 2 + sum(affine_atom^2)',
            'affine_square_count':len(atoms),'pooled_port_count':len(ports),
            'ports':ports,'scope':'exact coefficient identity and power-port coverage'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--equation',type=Path,required=True)
    ap.add_argument('--receipt',type=Path);a=ap.parse_args();result=check(a.equation)
    payload=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(payload)
    print(payload,end='')
