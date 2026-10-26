#!/usr/bin/env python3
"""Independent exact audit of the factorial-free source's frame and pools.

Uses integer polynomial dictionaries only. Imports no producer or optimizer.
Run with BASIS235 POOLED223 POOL_CERTIFICATE [--receipt OUTPUT].
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path


def plus(*polys):
    result = {}
    for p in polys:
        for mon, value in p.items():
            result[mon] = result.get(mon, 0) + value
    return {mon: value for mon, value in result.items() if value}


def times(p, q):
    result = {}
    for a, b in p.items():
        for c, d in q.items():
            mon = tuple(sorted(a+c))
            result[mon] = result.get(mon, 0) + b*d
    return {mon: value for mon, value in result.items() if value}


def neg(p):
    return {m: -c for m, c in p.items()}


def scale(c, p):
    return {m: c*v for m, v in p.items() if c*v}


def const(c):
    return {(): c} if c else {}


def decode(terms):
    result = {}
    for value, mon in terms:
        if type(value) is not int or not value:
            raise ValueError('bad coefficient')
        if any(type(i) is not int or i < 0 for i in mon):
            raise ValueError('bad variable index')
        key = tuple(sorted(mon))
        if key in result:
            raise ValueError('duplicate monomial')
        result[key] = value
    return result


def require_equal(p, q, label):
    if p != q:
        raise ValueError((label, plus(p, neg(q))))


def require_signed(p, q, label):
    if p != q and p != neg(q):
        raise ValueError((label, plus(p, neg(q))))


def check(base, pooled, cert):
    names = {v['name']: i for i, v in enumerate(base['variables'])}
    if len(names) != len(base['variables']):
        raise ValueError('duplicate variable names')
    def v(name):
        return {(names[name],): 1}
    def shift(name, offset):
        return plus(v(name), const(offset))
    rows = [decode(r['terms']) for r in base['residuals']]
    def row(label):
        matches = [p for p, r in zip(rows, base['residuals']) if r['label'] == label]
        if len(matches) != 1:
            raise ValueError(('nonunique row', label))
        return matches[0]

    t, F, x = v('t0'), v('crt.growth_majorant_F'), v('x')
    yp, C = v('y'), scale(2, v('crt.even_index_half'))
    q, qp = shift('pow2.output', -1), v('pow2.output')
    A = shift('shared.A', 1)
    idx = {0: t, 1: x, 2: x, 3: plus(F,t), 4: t,
           5: shift('crt.encoded.a', -1), 7: v('crt.encoded.b'),
           8: v('crt.encoded.c'), 9: v('crt.encoded.d'),
           10: v('crt.encoded.S'), 11: yp, 12: v('crt.encoded.Sp'),
           13: v('crt.encoded.u'), 14: x, 15: v('crt.encoded.vq'),
           16: C, 17: v('add.380')}
    plus_requests = [3,5,7,8,9,10,12,13,15,16,17]
    radix_requests = [4,11,14]
    bs = {0:t, 1:v('choose0.output'), 2:v('self_radix.BH')}
    bs.update({i:qp for i in plus_requests})
    bs.update({i:q for i in radix_requests})
    out = {i: F if i == 0 else q if i == 2 else v('pow%d.output'%i) for i in idx}

    # One duplicate t is inherited from the old growth-base slot d=t.
    atoms = [t,t,plus(F,t),plus(t,const(1)),x,yp,F,v('choose0.output'),
             shift('crt.encoded.a',-1)]
    atoms.extend(v('crt.encoded.'+s) for s in ['b','c','d','S','Sp','u','vq'])
    atoms.extend([C,v('pow1.output'),v('add.380'),q,qp,v('self_radix.BH')])
    atoms.extend(out[i] for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17])
    expected = plus(v('shared.W'),const(-2),*(neg(times(a,a)) for a in atoms))
    require_equal(row('shared.frame_definition'),expected,'36-square frame')
    for i in idx:
        for role, p in [('base',bs[i]),('index',idx[i]),('output',out[i])]:
            if p not in atoms:
                raise ValueError(('missing squared atom',i,role))
    require_equal(row('cofinal.horizon'),plus(t,const(-16),
                  scale(-4,times(v('cofinal.horizon_root'),v('cofinal.horizon_root')))),
                  'cofinal horizon')
    def require_present(p,label):
        if p not in rows:
            raise ValueError(('missing exact bootstrap row',label))
    require_present(plus(C,F,const(1),neg(times(v('choose0.output'),v('crt.index_quotient')))),
                    'odd B product')
    require_present(plus(x,neg(F),const(-1),neg(times(yp,v('endpoint.u0')))),
                    'first endpoint')
    Lbeta=plus(const(1),times(plus(t,const(1)),plus(yp,const(-1))))
    require_present(plus(v('mul.11'),neg(Lbeta)),'terminal divisor')
    require_present(plus(x,const(-1),neg(times(v('mul.11'),v('endpoint.ut')))),
                    'terminal endpoint')
    require_equal(row('bootstrap.beta_base_square_product'),
                  plus(yp,const(-1),neg(F),scale(-2,times(F,v('beta.odd_multiplier_half')))),
                  'actual affine odd beta multiplier')
    representatives=[C,shift('crt.encoded.a',-1)]
    representatives.extend(v('crt.encoded.'+s) for s in ['b','c','d','S','Sp','u','vq'])
    Hactual=plus(const(2),scale(4,plus(*representatives)))
    require_equal(row('self_radix.base_definition'),
                  plus(v('self_radix.BH'),neg(times(v('choose0.output'),Hactual))),
                  'actual parity-safe BH base')

    # The group certificate is checked against the actual old norm,
    # product and power rows, rather than trusted as a semantic declaration.
    pair_index = {0:t,2:plus(F,t),3:idx[5],5:idx[7],6:idx[8],7:idx[9],
                  8:idx[10],9:yp,10:idx[12],11:idx[13],12:x,
                  13:idx[15],14:C,15:idx[17]}
    request_pair = {3:2,4:0,5:3,7:5,8:6,9:7,10:8,11:9,
                    12:10,13:11,14:12,15:13,16:14,17:15}
    pairs = {}
    generated = []
    removed_rows = set()
    removed_variables = set()
    seen = set()
    for group in cert['groups']:
        expected_requests = plus_requests if group['group']=='radix_plus_one' else radix_requests
        if [r['request'] for r in group['requests']] != expected_requests:
            raise ValueError('wrong request block')
        n = bs[expected_requests[0]]
        require_equal(decode(group['base']),n,'actual pooled base')
        require_equal(decode(group['A']),A,'actual Pell parameter')
        T = plus(scale(2,times(A,n)),neg(times(n,n)),const(-1))
        require_equal(decode(group['T']),T,'old modulus expression')
        tv = {(group['modulus_coordinate'],):1}
        require_signed(rows[group['modulus_row']],plus(tv,neg(T)),'old modulus row')
        removed_rows.add(group['modulus_row'])
        removed_variables.add(group['modulus_coordinate'])
        H, S = {}, {}
        for r in group['requests']:
            i, p = r['request'], r['pair']
            if i in seen or request_pair[i] != p:
                raise ValueError('repeated or mismatched request')
            seen.add(i)
            Xi,Yi,Zi = (decode(r[k]) for k in ['X','Y','Z'])
            mi = out[i]
            require_equal(decode(r['output']),mi,'actual power output')
            require_equal(Xi,shift('index%d.X'%p,1),'actual canonical X')
            require_equal(Yi,shift('index%d.Y'%p,-1 if p==3 else 0),'actual canonical Y')
            require_signed(rows[r['retained_AY_row']],plus(Zi,neg(times(A,Yi))),'retained AY')
            require_equal(rows[r['retained_norm_row']],
                plus(times(Xi,Xi),times(Yi,Yi),neg(times(Zi,Zi)),const(-1)),
                'retained Pell norm')
            quotient = {(r['removed_quotient'],):1}
            error = plus(mi,neg(Xi),Zi,neg(times(n,Yi)))
            require_equal(rows[r['removed_row']],plus(error,times(tv,quotient)),
                          'old exact power congruence')
            removed_rows.add(r['removed_row'])
            removed_variables.add(r['removed_quotient'])
            pairs[p] = (Xi,Yi,Zi)
            H = plus(H,times(Yi,plus(mi,neg(Xi))))
            D = plus(mi,neg(Xi),Zi)
            S = plus(S,times(D,D),neg(times(Yi,Yi)))
        K,L = {(group['new_K'],):1},{(group['new_L'],):1}
        rr = [plus(K,scale(-2,H),neg(times(plus(scale(2,A),neg(n)),L))),
              plus(S,neg(times(n,K)),L)]
        if len(group['new_rows']) != 2:
            raise ValueError('wrong pool row count')
        for actual, expected in zip(group['new_rows'],rr):
            require_equal(decode(actual['terms']),expected,'literal pooled row')
        generated.extend(rr)

    if set(pairs) != set(pair_index):
        raise ValueError('missing principal signed-index pair')
    # This checks that the claimed indices actually occur in the retained
    # signed orientation/recovery aggregate, including every affine offset.
    index_norm = plus(*(plus(times(plus(Xi,const(-1)),plus(Xi,const(-1))),
                            times(plus(Yi,neg(pair_index[p])),plus(Yi,neg(pair_index[p]))))
                       for p,(Xi,Yi,Zi) in sorted(pairs.items())))
    index_norm = plus(index_norm,neg(times(v('shared.A'),v('cap.pooled_quotient'))))
    require_equal(row('cap.pooled_index_residue'),index_norm,'canonical index aggregate')
    for i,p in [(0,0),(1,12),(2,12)]:
        Xi,Yi,Zi=pairs[p]
        n=bs[i]
        T=plus(scale(2,times(A,n)),neg(times(n,n)),const(-1))
        tv=v('base%d.T'%i)
        if plus(tv,neg(T)) not in rows and plus(T,neg(tv)) not in rows:
            raise ValueError(('missing individual modulus',i))
        require_present(plus(out[i],neg(Xi),Zi,neg(times(n,Yi)),
                             times(tv,v('pow%d.quotient'%i))),
                        'individual power '+str(i))

    if removed_rows != set(cert['removed_rows']) or removed_variables != set(cert['removed_variables']):
        raise ValueError('removed slots do not match the audited requests')
    mapping = dict(cert['old_to_new'])
    if len(mapping) != len(pooled['variables']) or sorted(mapping.values()) != list(range(len(mapping))):
        raise ValueError('coordinate map is not a bijection of retained slots')
    kept_old = set(range(len(base['variables'])))-removed_variables
    new_slots = {g[k] for g in cert['groups'] for k in ['new_K','new_L']}
    if set(mapping) != kept_old | new_slots:
        raise ValueError('unaudited coordinate deletion')
    def remap(p):
        return {tuple(sorted(mapping[i] for i in m)):c for m,c in p.items()}
    expected_rows = [remap(r) for i,r in enumerate(rows) if i not in removed_rows]
    expected_rows += [remap(r) for r in generated]
    actual_rows = [decode(r['terms']) for r in pooled['residuals']]
    if len(expected_rows) != len(actual_rows):
        raise ValueError('wrong emitted row count')
    for i,(p,r) in enumerate(zip(expected_rows,actual_rows)):
        require_equal(p,r,'emitted pooled residual '+str(i))
    return {'status':'PASS','square_atoms':len(atoms),'power_requests':len(idx),
            'principal_canonical_pairs':len(pairs),'pool_requests':len(seen),
            'removed_power_or_modulus_rows':len(removed_rows),
            'new_pooled_rows':len(generated),'old_variables':len(base['variables']),
            'new_variables':len(pooled['variables']),'new_residuals':len(actual_rows),
            'checks':['exact squared frame','all actual base/index/output memberships',
                      'actual parity-safe bootstrap equations','all three retained individual power requests',
                      'actual canonical signed-index aggregate','retained Pell norms and AY rows',
                      'all deleted power congruences and moduli','both two-row pool identities',
                      'every emitted pooled residual and all retained coordinates'],
            'scope':'Finite exact arithmetic; canonical signed-index and |A|>W^W semantics remain the identified inherited ordinary theorems.'}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('base',type=Path)
    ap.add_argument('pooled',type=Path)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    raw=[p.read_bytes() for p in [args.base,args.pooled,args.certificate]]
    data=[json.loads(b) for b in raw]
    if data[2]['parent_equation_sha256'] != hashlib.sha256(raw[0]).hexdigest():
        raise ValueError('certificate parent hash')
    result=check(*data)
    controls=[]
    for kind in ['frame','pair_offset','emitted_pool']:
        changed=copy.deepcopy(data)
        if kind=='frame':
            r=next(r for r in changed[0]['residuals'] if r['label']=='shared.frame_definition')
            r['terms'][0][0]+=1
        elif kind=='pair_offset':
            changed[2]['groups'][0]['requests'][1]['Y'][0][0]=1
        else:
            changed[1]['residuals'][-1]['terms'][0][0]*=2
        try:
            check(*changed)
        except ValueError:
            controls.append(kind)
        else:
            raise ValueError(('corruption control accepted',kind))
    result['rejected_corruption_controls']=controls
    result['sha256']={k:hashlib.sha256(b).hexdigest()
                       for k,b in zip(['base','pooled','certificate'],raw)}
    text=json.dumps(result,indent=2)+'\n'
    if args.receipt:
        args.receipt.write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()
