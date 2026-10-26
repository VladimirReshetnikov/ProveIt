#!/usr/bin/env python3
"""Explicit Start-only native constants and finite arithmetic certificate.

No external packages, imported repository implementation, or network access.
"""
from pathlib import Path
from math import gcd, lcm, isqrt
import argparse, hashlib, json

HERE = Path(__file__).resolve().parent
RHO, M = 1 << 47, 1 << 44
FLAG, LOW, HIGH, PADDING = 1031, 2042, 3074, 4106
SEED = (
    'BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y'
    'iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U'
    'OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq'
    '4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ'
    'FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F'
    'We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl'
    '0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ8P'
)
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'


def need(ok, text):
    if not ok:
        raise ValueError(text)


def enc(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def least_factor(n):
    if n < 2:
        return 1
    if n % 2 == 0:
        return None if n == 2 else 2
    for p in range(3, isqrt(n) + 1, 2):
        if n % p == 0:
            return p
    return None


def factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def order(a, p):
    need(least_factor(p) is None and a % p, 'Order at a prime for a unit')
    n = p - 1
    for d in factors(n):
        while n % d == 0 and pow(a, n // d, p) == 1:
            n //= d
    need(pow(a, n, p) == 1, 'Full order')
    tests = {str(d): pow(a, n // d, p) for d in factors(n)}
    need(all(v != 1 for v in tests.values()), 'Every prime proper-order test')
    return {'order': n, 'prime_factors': factors(n), 'proper_residues': tests}


def language():
    need(len(SEED) == 436, 'Whole436-character seed')
    A = 0
    for s in SEED:
        A = 62 * A + ALPHABET.index(s)
    N, T, E = A % (1 << 636), (A >> 636) % (1 << 1675), A >> 2311
    bit = lambda v, i: (v >> i) & 1
    digit = lambda v, b, i: (v // b ** i) % b
    actions = []
    sigmas = [sum(bit(N, k) for k in range(j)) for j in range(430)]
    for j in range(430):
        q, b = divmod(j, 2)
        nu = bit(N, j)
        m = bit(N, 430 + q)
        tq = sum(bit(N, 430 + k) for k in range(q))
        F = 14 + m * (digit(E, 16, tq) - 14)
        u = nu * (1 + sigmas[j]) + (1 - nu) * digit(T, 216, j - sigmas[j])
        actions.append((u, bit(F, 2 * b), bit(F, 2 * b + 1)))
    S = [sorted({u for u, v, d in actions if d == e}) for e in (0, 1)]
    rank = lambda d, q: 205 - 199 * d + sum(x < q for x in S[d])
    h = lambda q, b: 2 * q + b + 2
    tiles = {}
    def tile(i, t):
        need(i not in tiles, 'Unique tile index')
        tiles[i] = tuple(t)
    tile(0, (2, 435, 3, 1))
    tile(1, (5, 0, 0, 0))
    for j, (u, v, d) in enumerate(actions):
        q, b = divmod(j, 2)
        tile(j + 2, ((1-d)*rank(0,u), h(q,b), d*rank(1,u), v))
    for a in range(2):
        for b in range(2):
            tile(434-2*a+b, (0,432*a+b,0,432*a+b))
            tile(924+2*a+b, (0,432*a+b,0,438))
    for d in range(2):
        for q in S[d]:
            r = rank(d,q)
            for b in range(2):
                tile(424+2*r+b, (d*r,b,(1-d)*r,h(q,b)))
    for i, t in enumerate(((2,434,2,0),(3,436,4,4),(4,436,4,0)),928):
        tile(i,t)
    for t in (434,435,436):
        tile(497+t,(1,438,1,t))
    for a in range(3):
        for b in range(3):
            tile(934+3*a+b,(a*a,437,b,437))
    need(set(tiles) == set(range(943)), 'Complete943-tile language')
    ts = [tiles[i] for i in range(943)]
    coeff = [0] * 3297
    for j,(w,n,p,s) in enumerate(ts):
        coeff[j] = 1 + 1024 * (1+w+256*n+131072*p+33554432*s)
    for start,bits,count in ((943,35,9),(973,18,9),(992,27,8),(1002,10,8)):
        for j in range(count):
            coeff[start+j] = 1 << (bits+j)
    E0 = set(range(943)) | set(range(943,952)) | set(range(973,982))
    E0 |= set(range(992,1000)) | set(range(1002,1010)) | {990,991,FLAG}
    need(len(E0) == 980 and sum(bool(x) for x in coeff) == 977, 'Physical and weighted supports')
    inherited = json.loads((HERE/'inherited/coefficients.json').read_text())
    need(coeff == inherited, 'All3297 weights equal inherited complete decoded language')
    need(max(coeff) < M and sum(coeff[943:]) == M-1024, 'Whole clause weight bounds')
    return actions, ts, coeff, E0


def kernel(c):
    dc = {}
    for center in (LOW,HIGH):
        for e,v in enumerate(c):
            if v:
                need(center-e not in dc, 'Reflected coefficients disjoint')
                dc[center-e] = v
    for e in (20,30,FLAG):
        need(e not in dc, 'Bare kernels disjoint')
        dc[e] = 1
    return dc


def geometry(c,E0,L):
    dc = kernel(c)
    def hits(t):
        return sorted((e,dc[t-e]) for e in E0 if t-e in dc)
    checks = {}
    def check(n,a,b):
        need(a == b, n)
        checks[n] = {'actual':a,'expected':b,'pass':True}
    check('one_Start_copy', hits(FLAG), [(0,1)])
    for j in range(9):
        check('temporal_copy_'+str(j),hits(973+j),[(943+j,1)])
        check('temporal_no_spatial_'+str(j),973+j-10 in E0,False)
    for j in range(8):
        check('spatial_copy_'+str(j),hits(1012+j),[(992+j,1)])
        check('spatial_source_'+str(j),1012+j-10,1002+j)
    check('flag_no_spatial',FLAG-10 in E0,False)
    check('flag_no_bare',[e for e in (FLAG-20,FLAG-30) if e in E0],[])
    clause=sorted((e,c[e]) for e in E0 if c[e])
    adjacent=sorted((e,c[e+1]) for e in E0 if c[e+1])
    check('lower_clause',hits(LOW),clause)
    check('upper_clause',hits(HIGH),clause)
    check('lower_predecessor',hits(LOW-1),adjacent)
    check('upper_predecessor',hits(HIGH-1),sorted(adjacent+[(FLAG,c[0])]))
    check('no_clause_spatial',[x for x in (LOW,LOW-1,HIGH,HIGH-1) if x-10 in E0],[])
    check('no_clause_temporal',[x for x in (LOW,LOW-1,HIGH,HIGH-1) if x in E0],[])
    check('first_reflected',min(e for e in dc if e not in (20,30,FLAG)),1033)
    check('last_product',max(dc)+max(E0),4105)
    check('last_hits',hits(4105),[(FLAG,c[0])])
    check('padding_and_tail_zero',[(t,hits(t)) for t in range(4106,L) if hits(t)],[])
    check('padding_and_tail_spatial',[t for t in range(4106,L) if t-10 in E0],[])
    check('padding_fits',PADDING+18 < L,True)
    targets=list(range(974,982))+[FLAG]
    admissible=[]
    typed=[]
    for r in range(L):
        pre=[((t-r)%L,(t-r)//L) for t in targets]
        if all(e in E0 for e,_ in pre):
            cells={z for _,z in pre}
            if all(sum(e<=942 and z==k for e,z in pre)<=1 for k in cells):
                admissible.append(r)
                possible=True
                for k in cells:
                    selectors=[e for e,z in pre if z==k and e<=942]
                    if selectors:
                        tile=selectors[0]
                        packed=(c[tile]-1)//1024-1
                        colors=[(943,9,511-((packed>>25)&511)),
                                (973,9,511-((packed>>8)&511)),
                                (992,8,255-(packed&255)),
                                (1002,8,255-((packed>>17)&255))]
                        for e,z in pre:
                            if z!=k:continue
                            for start,width,value in colors:
                                if start<=e<start+width and not ((value>>(e-start))&1):
                                    possible=False
                if possible:typed.append(r)
    check('support_only_digit_offsets',admissible,[0,32])
    check('all_decoded_tile_offsets_unique',typed,[0])
    starts=[u for u in range(L-7) if all(u+j in E0 for j in range(8))
            and sum(u+j<=942 for j in range(8))<=1]
    check('eight_block_starts',starts,[942,943,944,973,974,990,991,992,1002])
    check('ninth_target_leaves_two_starts',[u for u in starts if u+57 in E0],[942,974])
    check('tile942_old_south',((c[942]-1)//1024-1)>>25,437)
    check('tile942_complement_south_low_bit',(511-437)&1,0)
    check('initial_band_no_carry',9+3*RHO//4+29 < RHO,True)
    maxadj=max(c[e+1] for e in E0 if e<943)+sum(c[e+1] for e in E0 if e>=943)
    check('adjacent_bound',maxadj <= 2*M-1024,True)
    check('upper_predecessor_reset',2*M-1024+c[0]+29 < RHO,True)
    envelope=[0]*(4105+1)
    for e in E0:
        for t,v in dc.items():
            envelope[e+t]+=v
    for t,v in dc.items():
        envelope[990+t]+=2*v
    peak=max(envelope)
    check('whole_global_carry29',peak+3+3*RHO//4+29 <30*RHO,True)
    check('safe_dummy_max',max(dc)+990,4064)
    check('safe_dummy_three_digit_margin',L-4065>=3,True)
    check('clause_gap_absent',[(x,y) for x in E0 for y in E0 if x-y==1043],[])
    return {'checks':checks,'dc_terms':len(dc),'physical_count':len(E0),
            'weighted_count':sum(bool(x) for x in c),'coefficient_sum':sum(c),
            'boolean_plus_extra_convolution_peak':peak,'last_product':4105}


def constants(c,E0,L):
    p=lambda e:1<<(47*e)
    B=p(L); beta=B-1
    dc=sum(v*p(e) for e,v in kernel(c).items())
    K=dc+p(L+10)
    MC=beta-sum(p(e) for e in E0 if e != 1)-2*p(990)
    core=sum(p(973+j) for j in range(9))+sum(p(1012+j) for j in range(8))+p(FLAG)
    padding=(1<<29)*p(PADDING+18)-p(PADDING)
    MF0=4+(M-2)*(p(LOW)+p(HIGH))+core+padding
    need(0<dc<B and 0<MC<beta and 0<MF0<beta,'Whole scalar boxes')
    need(MC%4==2 and MF0%8==4,'Whole origin residues')
    need(MF0.bit_count()==980 and MC.bit_count()==47*L-980,'Complementary mask populations')
    return {'beta':beta,'K0':K,'MC':MC,'MF':MF0+beta}


def modular(c,L,p):
    power=lambda e:pow(2,47*e,p)
    r=power(1);rinv=pow(r,-1,p)
    phi=0
    for v in reversed(c):
        phi=(phi*rinv+v)%p
    bare=power(20)+power(30)+power(FLAG)+power(L+10)
    K=(bare+(power(LOW)+power(HIGH))*phi)%p
    direct=(sum(v*power(e) for e,v in kernel(c).items())+power(L+10))%p
    need(K==direct,'Independent dense and sparse modular evaluation')
    B=power(L)
    return {'p':p,'B':B,'K':K,'B_squared':B*B%p,'H':(1+B*K+B*B)%p}


def controller(c,E0):
    trials=[]
    for L in range(PADDING+20,PADDING+221):
        d=47*L
        row={'L':L,'least_factor':least_factor(L)};trials.append(row)
        if row['least_factor'] is not None or L==47:
            continue
        fixed=[]
        for p in (47,L):
            v=modular(c,L,p)
            v['order2']=order(2,p);v['orderB']=order(v['B'],p)
            fixed.append(v)
        row['fixed']=fixed
        if any(v['H']==0 or v['B_squared']==1 or gcd(d,v['orderB']['order'])!=1 for v in fixed):
            row['rejected']='fixed units or order coprimality';continue
        spacing=lcm(*(v['orderB']['order'] for v in fixed))
        aux=[]
        for j in range(d//spacing+1,d//spacing+502):
            lam=spacing*j+1
            a={'multiplier':j,'p':lam,'least_factor':least_factor(lam)};aux.append(a)
            if a['least_factor'] is not None:continue
            a.update(modular(c,L,lam))
            lift=pow(2,d*(lam-1),lam*lam)
            a['lift']=lift;a['lift_quotient']=(lift-1)//lam
            if a['B_squared']!=1 and a['H']!=0 and a['lift_quotient']:
                need(lift%lam==1 and lam>d and (lam-1)%spacing==0,'Controller lift and divisibility')
                return {'L':L,'d':d,'spacing':spacing,'fixed':fixed,'lambda':lam,'auxiliary':a,
                        'length_trials':trials,'auxiliary_trials':aux}
        row['rejected']='bounded auxiliary search'
    raise ValueError('No controller in bounded search')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    actions,tiles,c,E0=language();ctl=controller(c,E0);L=ctl['L']
    geo=geometry(c,E0,L);ports=constants(c,E0,L)
    portmeta={}
    for n,v in ports.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'big')
        portmeta[n]={'bits':v.bit_length(),'bytes':len(raw),'sha256':sha(raw)}
        for row in ctl['fixed']+[ctl['auxiliary']]:
            if n=='K0':need(v%row['p']==row['K'],'Whole K modular cross-check')
    data={'schema':'start-only-native-v1','controller':ctl,'geometry':geo,'ports':portmeta,
          'raw_bytes':sum(x['bytes'] for x in portmeta.values()),'seed_sha256':sha(SEED.encode()),
          'actions_sha256':sha(enc(actions)),'tiles_sha256':sha(enc(tiles)),
          'coefficients_sha256':sha(enc(c)),'script_sha256':sha(Path(__file__).read_bytes())}
    graph=json.loads((HERE/'inherited/polynomial.json').read_text())
    known=set(graph['witnesses'])|set(graph['fixed_numerals'])
    byname={};counts={'+':0,'-':0,'*':0}
    for name,op,a,b in graph['source']:
        need(name not in known and op in counts,'Closed distinct gate')
        need(all(isinstance(v,int) or v in known for v in (a,b)),'Topological order')
        known.add(name);byname[name]=(a,b);counts[op]+=1
    live=set();stack=[graph['output']]
    while stack:
        v=stack.pop()
        if isinstance(v,int) or v in live:continue
        live.add(v);stack.extend(byname.get(v,()))
    need(live==known and counts=={'+':15,'-':13,'*':38},'All66 gates,15 witnesses,4 ports live')
    graph['name']='start_only4127_p66_degree157'
    graph['proof']='START_ONLY_PROOF.md'
    graph['proof_boundary']='Ordinary new native proof and finite controller; retained P66 and refutation calibration.'
    graph['coefficient_binding']={
        'schema':'start_only4127_materialized_v1','path':'start_only_ports/',
        'certificate':'start_only_certificate.json','certificate_sha256':sha(enc(data)),
        'ordinary_proof':'START_ONLY_PROOF.md',
        'ordinary_proof_sha256':sha((HERE/'START_ONLY_PROOF.md').read_bytes()),
        'ports':{n:{**m,'file':n+'.bin'} for n,m in portmeta.items()},
        'raw_bytes':data['raw_bytes']}
    path=HERE/'start_only_certificate.json'
    if args.write:
        path.write_bytes(enc(data));(HERE/'start_only_tiles.json').write_bytes(enc(tiles))
        (HERE/'start_only_coefficients.json').write_bytes(enc(c))
        (HERE/'start_only_polynomial.json').write_bytes(enc(graph))
        (HERE/'start_only_ports').mkdir(exist_ok=True)
        for n,v in ports.items():
            (HERE/'start_only_ports'/f'{n}.bin').write_bytes(v.to_bytes((v.bit_length()+7)//8,'big'))
    else:
        need(path.read_bytes()==enc(data),'Exact deterministic certificate')
        need((HERE/'start_only_tiles.json').read_bytes()==enc(tiles),'Exact complete tiles')
        need((HERE/'start_only_coefficients.json').read_bytes()==enc(c),'Exact complete weights')
        need((HERE/'start_only_polynomial.json').read_bytes()==enc(graph),'Exact complete P66 graph and new binding')
        for n,v in ports.items():
            need(int.from_bytes((HERE/'start_only_ports'/f'{n}.bin').read_bytes(),'big')==v,'Exact complete coefficient')
    print(json.dumps({'status':'PASS','L':L,'d':47*L,'lambda':ctl['lambda'],
                      'spacing':ctl['spacing'],'H':[x['H'] for x in ctl['fixed']]+[ctl['auxiliary']['H']],
                      'raw_bytes':data['raw_bytes'],'dc_terms':geo['dc_terms']},sort_keys=True))


if __name__=='__main__':main()
