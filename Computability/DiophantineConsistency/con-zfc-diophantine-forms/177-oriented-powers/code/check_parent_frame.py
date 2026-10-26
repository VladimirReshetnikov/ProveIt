#!/usr/bin/env python3
"""Independently reconstruct the P225 frame from actual semantic atom squares.

Adapted, with attribution, from ProveIt report 158-pooled-powers,
code/check_all_frame_atoms.py, snapshot
0c48d332df6b0e50d4e5b6251c531898f5682c72. The inherited algebraic check is
retained; this wrapper adds a default local source and its exact byte pin.
The original license and the package's notices apply.
This finite check establishes the frame identity and request membership,
not the unbounded Pell-frame theorem or logical calibration.
"""
from pathlib import Path
from collections import defaultdict
import json, hashlib, argparse
ROOT=Path(__file__).resolve().parent.parent
PIN='fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56'


def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items(): out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(a,p): return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
    out=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}
def main(path):
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PIN:raise ValueError('Frozen P225 frame source identity differs')
    eq=json.loads(raw);names={v['name']:i for i,v in enumerate(eq['variables'])}
    def v(name):return {(names[name],):1}
    def c(a):return {():a} if a else {}
    def shifted(name,a):return add(v(name),c(a))
    t=v('t0');fsq=v('mul.1');q=shifted('pow2.output',-1)
    # These are actual semantic atoms, not merely stored variable names.
    atoms=[('t',t),('t+1',add(t,c(1))),('F^2+t',add(fsq,t)),
           ('x',v('x')),('F^2+1',add(fsq,c(1))),('B',v('choose0.output')),
           ('V',v('pow0.output')),('y+1=V',v('pow0.output')),
           ('a',shifted('crt.encoded.a',-1))]
    for name in ['b','c','d','S','Sp','u','vq']:
        atoms.append((name,v('crt.encoded.'+name)))
    atoms += [('C',v('crt.encoded_index_minus_one')),('N',v('pow1.output')),
              ('h',v('add.380')),('q',q),('q+1',v('pow2.output')),
              ('BH',v('self_radix.BH'))]
    for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]:
        atoms.append(('pow'+str(i)+'.output',v('pow'+str(i)+'.output')))
    reconstructed=add(v('shared.W'),c(-2),*(scale(-1,mul(a,a)) for _,a in atoms))
    frame=[r for r in eq['residuals'] if r['label']=='shared.frame_definition']
    if len(frame)!=1: raise ValueError('expected one frame row')
    actual={tuple(m):c for c,m in frame[0]['terms']}
    if actual!=reconstructed:
        raise ValueError('frame atom identity failed: '+str(add(actual,scale(-1,reconstructed))))
    # Match every power group's actual base, output, and requested exponent.
    request_indices={0:t,1:v('x'),2:v('x'),3:add(fsq,t),4:t,
      5:shifted('crt.encoded.a',-1),7:v('crt.encoded.b'),8:v('crt.encoded.c'),
      9:v('crt.encoded.d'),10:v('crt.encoded.S'),11:v('pow0.output'),
      12:v('crt.encoded.Sp'),13:v('crt.encoded.u'),14:v('x'),
      15:v('crt.encoded.vq'),16:v('crt.encoded_index_minus_one'),17:v('add.380')}
    base_by_request={0:add(fsq,c(1)),1:v('choose0.output'),2:v('self_radix.BH')}
    for i in [3,5,7,8,9,10,12,13,15,16,17]:base_by_request[i]=v('pow2.output')
    for i in [4,11,14]:base_by_request[i]=q
    outputs={i:(q if i==2 else v('pow'+str(i)+'.output')) for i in request_indices}
    atom_values=[a for _,a in atoms]
    for i,k in request_indices.items():
        for role,a in [('base',base_by_request[i]),('index',k),('output',outputs[i])]:
            if a not in atom_values: raise ValueError(('missing actual atom',i,role,a))
    result={'status':'PASS','equation_sha256':hashlib.sha256(raw).hexdigest(),
      'frame_identity':'W=2+sum(atom^2)','actual_atom_count':len(atoms),
      'power_requests_covered':sorted(request_indices),'count':len(request_indices),
      'each_actual_base_index_output_square_strictly_below_W':True,
      'translations_checked':{'t0':'actual t','crt.encoded.a':'actual a + 1','pow2.output':'q+1','crt.encoded_index_minus_one':'actual C','add.380':'actual h','pow0.output':'V=y+1'},
      'atom_polynomials':[{ 'label':label,'terms':[[coef,list(mon)] for mon,coef in sorted(a.items())]} for label,a in atoms]}
    print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('equation',type=Path,nargs='?',default=ROOT/'sources/parent225.json');args=ap.parse_args();main(args.equation)

