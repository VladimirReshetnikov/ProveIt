#!/usr/bin/env python3
"""Read-only literal audit of source 172's pre-row-reduction 216 chart.

This is a finite interface check, not a proof of its unbounded semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
from collections import defaultdict

HERE = Path(__file__).resolve().parent
DEFAULT = HERE.parent / 'inputs/source216.json'

def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m,c in p.items(): out[m] += c
    return {m:c for m,c in out.items() if c}
def scale(c,p): return {m:c*v for m,v in p.items() if c*v}
def sub(p,q): return add(p,scale(-1,q))
def mul(p,q):
    out=defaultdict(int)
    for m,a in p.items():
        for n,b in q.items(): out[tuple(sorted(m+n))]+=a*b
    return {m:c for m,c in out.items() if c}
def C(c): return {():c} if c else {}
def V(i): return {(i,):1}
def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]
def parse(ts): return {tuple(m):c for c,m in ts}
def sq(p): return mul(p,p)
def require(test, label):
    if not test: raise ValueError(label)

def audit(path):
    raw=path.read_bytes(); src=json.loads(raw)
    rows=[parse(r['terms']) for r in src['residuals']]
    names={v['name']:i for i,v in enumerate(src['variables'])}
    def N(name,shift=0): return add(V(names[name]),C(shift))
    def hit(p,label):
        hits=[(j,1 if r==p else -1) for j,r in enumerate(rows) if r==p or r==scale(-1,p)]
        require(len(hits)==1,(label,hits))
        return {'row':hits[0][0],'sign':hits[0][1]}
    t=N('t0'); F=N('crt.growth_majorant_F'); B=N('choose0.output')
    A=N('shared.A',1); q=add(C(1),scale(4,N('radix.odd_square_root_half')))
    x=N('x'); y1=N('y'); BH=N('self_radix.BH')
    J=add(scale(5,N('crt.encoded.a')),scale(-3,N('crt.encoded.b')),
          scale(4,N('mul.40')),*(scale(2,N(n)) for n in
          ['add.61','radical218.27','add.101','radical219.32','add.142','mul.159','add.181','add.199','mul.311']),
          scale(4,N('add.156')),scale(4,N('add.308')))
    index={0:t,2:add(t,F),3:N('crt.encoded.a',-1),5:N('crt.encoded.b'),
           6:N('crt.encoded.c'),7:N('crt.encoded.d'),8:N('crt.encoded.S'),
           9:y1,10:N('crt.encoded.Sp'),11:N('crt.encoded.u'),12:x,
           13:N('crt.encoded.vq'),14:N('crt.encoded_index_minus_one'),15:J}
    znames={0:'mul.460',2:'mul.503',3:'mul.529',5:'mul.554',6:'mul.567',7:'mul.580',
            8:'mul.593',9:'mul.606',10:'mul.619',11:'mul.632',12:'mul.645',13:'mul.658',14:'mul.671',15:'mul.684'}
    pairs={}
    for i,k in index.items():
        d=N(f'index{i}.X_minus_AY'); yy=N(f'index{i}.Y',-1 if i==3 else 0)
        z=N(znames[i],1 if i==12 else 0); xx=add(d,z)
        pairs[i]={'D':d,'X':xx,'Y':yy,'Z':z,'k':k,
                  'AY':hit(sub(z,mul(A,yy)),f'AY{i}'),
                  'norm':hit(add(sq(d),scale(2,mul(d,z)),sq(yy),C(-1)),f'norm{i}')}
    requests=[(0,0,t,F),(1,12,B,N('pow1.output')),(2,12,BH,q),
              (3,2,add(q,C(1)),N('pow3.output')),(4,0,q,N('pow4.output')),
              (5,3,add(q,C(1)),N('pow5.output')),
              (7,5,add(q,C(1)),N('pow7.output')),(8,6,add(q,C(1)),N('pow8.output')),
              (9,7,add(q,C(1)),N('pow9.output')),(10,8,add(q,C(1)),N('pow10.output')),
              (11,9,q,N('pow11.output')),(12,10,add(q,C(1)),N('pow12.output')),
              (13,11,add(q,C(1)),N('pow13.output')),(14,12,q,N('pow14.output')),
              (15,13,add(q,C(1)),N('pow15.output')),(16,14,add(q,C(1)),N('pow16.output')),
              (17,15,add(q,C(1)),N('pow17.output'))]
    request_objects=[]
    for pno,i,n,m in requests:
        pair=pairs[i]; error=sub(sub(m,pair['D']),mul(n,pair['Y']))
        request_objects.append({'request':pno,'pair':i,'n':n,'m':m,'k':pair['k'],
                                'D':pair['D'],'X':pair['X'],'Y':pair['Y'],'Z':pair['Z'],'error':error})
    byrequest={r['request']:r for r in request_objects}
    blocks=[]; deleted_rows=set(); deleted_variables=set()
    for j in range(3):
        r=byrequest[j]; n=r['n']; T=sub(sub(scale(2,mul(A,n)),sq(n)),C(1))
        tv=N(f'base{j}.T'); Q=N(f'pow{j}.quotient')
        modulus=hit(sub(tv,T),f'modulus{j}')
        congruence=hit(add(r['error'],mul(tv,Q)),f'congruence{j}')
        deleted_rows.update([modulus['row'],congruence['row']])
        deleted_variables.update([names[f'base{j}.T'],names[f'pow{j}.quotient']])
        blocks.append({'name':f'singleton{j}','requests':[j],'base':n,'T':T,
                       'removed_rows':[modulus,congruence],
                       'removed_variables':[names[f'base{j}.T'],names[f'pow{j}.quotient']]})
    for label,pnos,n in [('radix_plus_one',[3,5,7,8,9,10,12,13,15,16,17],add(q,C(1))),('radix',[4,11,14],q)]:
        K=N(label+'.K'); L=N(label+'.L')
        H=add(*(mul(byrequest[p]['Y'],sub(byrequest[p]['m'],byrequest[p]['X'])) for p in pnos))
        S=add(*(sub(sq(sub(byrequest[p]['m'],byrequest[p]['D'])),sq(byrequest[p]['Y'])) for p in pnos))
        r1=hit(sub(sub(K,scale(2,H)),mul(sub(scale(2,A),n),L)),label+'K')
        r2=hit(add(S,scale(-1,mul(n,K)),L),label+'L')
        deleted_rows.update([r1['row'],r2['row']]); deleted_variables.update([names[label+'.K'],names[label+'.L']])
        blocks.append({'name':label,'requests':pnos,'base':n,'T':sub(sub(scale(2,mul(A,n)),sq(n)),C(1)),
                       'removed_rows':[r1,r2],'removed_variables':[names[label+'.K'],names[label+'.L']]})
    atoms=[t,add(t,F),x,y1,F,B]
    atoms += [N('crt.encoded.'+n,-1 if n=='a' else 0) for n in ['a','b','c','d','S','Sp','u','vq']]
    atoms += [N('crt.encoded_index_minus_one'),N('pow1.output'),J,q,add(q,C(1)),BH]
    atoms += [N('pow'+str(i)+'.output') for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]]
    frame=hit(sub(N('shared.W'),add(C(2),*(sq(a) for a in atoms))),'exact frame')
    require(len(atoms)==34,'34 frame atoms')
    for r in request_objects:
        for field in ['n','m','k']:
            require(r[field] in atoms,(r['request'],field,'missing from frame'))
    oriented=add(*(add(sq(sub(p['X'],C(1))),sq(sub(p['Y'],p['k']))) for p in pairs.values()),
                 scale(-1,mul(sub(A,C(1)),N('cap.pooled_quotient'))))
    norms=add(*(add(sq(p['X']),sq(p['Y']),scale(-1,sq(p['Z'])),C(-1)) for p in pairs.values()))
    orientation=hit(sub(oriented,norms),'orientation minus retained norms')
    require(not deleted_rows.intersection({frame['row'],orientation['row']}),'kept frame/orientation')
    for i,p in pairs.items():
        require(not deleted_rows.intersection({p['AY']['row'],p['norm']['row']}),(i,'kept pair'))
    for j,r in enumerate(rows):
        if j not in deleted_rows:
            require(not any(v in deleted_variables for m in r for v in m),('private variable leakage',j))
    for r in request_objects:
        for field in ['n','m','k','D','X','Y','Z']:
            require(not any(v in deleted_variables for m in r[field] for v in m),('request private dependency',r['request'],field))
    result={'schema':'source172_affine216_mixed_pool_interface_v1','source_path':str(path.resolve()),
            'source_sha256':hashlib.sha256(raw).hexdigest(),'source_variables':len(src['variables']),
            'source_rows':len(rows),'A':terms(A),'q':terms(q),'J':terms(J),
            'deleted_rows':sorted(deleted_rows),'deleted_variables':sorted(deleted_variables),
            'retained_rows':[j for j in range(len(rows)) if j not in deleted_rows],
            'retained_variables':[j for j in range(len(src['variables'])) if j not in deleted_variables],
            'blocks':[{**{k:v for k,v in b.items() if k not in ['base','T']},'base':terms(b['base']),'T':terms(b['T'])} for b in blocks],
            'requests':[{k:terms(v) if k not in ['request','pair'] else v for k,v in r.items()} for r in request_objects],
            'pairs':[{**{k:terms(v) for k,v in p.items() if k not in ['AY','norm']},'pair':i,'AY':p['AY'],'norm':p['norm']} for i,p in pairs.items()],
            'frame':{**frame,'atoms':[terms(a) for a in atoms]},'orientation':orientation,
            'all_private_occurrences_confined_to_deleted_rows':True,
            'all_frame_atoms_and_pair_orientations_retained':True,
            'result_with_one_new_coordinate':{'variables':len(src['variables'])-len(deleted_variables)+1,'quadratic_rows':len(rows)-len(deleted_rows),'new_aggregate_rows':1}}
    return result

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--source',type=Path,default=DEFAULT);ap.add_argument('--output',type=Path)
    args=ap.parse_args();result=audit(args.source)
    if args.output: args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','source_sha256':result['source_sha256'],'result':result['result_with_one_new_coordinate'],'frame':result['frame']['row'],'orientation':result['orientation']['row'],'deleted_rows':result['deleted_rows'],'deleted_variables':result['deleted_variables']},sort_keys=True,indent=2))
if __name__=='__main__': main()
