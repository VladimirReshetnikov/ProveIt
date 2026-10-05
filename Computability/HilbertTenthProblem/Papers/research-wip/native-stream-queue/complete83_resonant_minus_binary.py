#!/usr/bin/env python3
"""New proof corroborator. Frozen inputs are read only as inert data."""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS = {
 'complete83_fixed_prime_quotient_carries.md':'53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46',
 'complete83_subpower_selector_bound.md':'3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4',
 'complete83_source_coupled_input_lifting.md':'822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
 'complete83_outer_family_sparse_two_primary.md':'bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97',
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
 'FIXED_RAW_UNIVERSAL_77_PROOF.md':'292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41',
 'FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}

def require(ok, label):
    if not ok:
        raise ValueError(label)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()

# Independent sparse polynomial arithmetic in (Q,m,K,U,V,h).
ZERO = (0,)*6
def constant(n):
    return {ZERO:n} if n else {}
def variable(i):
    a = [0]*6
    a[i] = 1
    return {tuple(a):1}
def add(*polys):
    out = {}
    for p in polys:
        for mon, coefficient in p.items():
            out[mon] = out.get(mon, 0)+coefficient
    return {mon:c for mon,c in out.items() if c}
def scale(p, n):
    return {mon:n*c for mon,c in p.items() if n*c}
def mul(*polys):
    out = constant(1)
    for p in polys:
        nxt = {}
        for a,x in out.items():
            for b,y in p.items():
                mon = tuple(i+j for i,j in zip(a,b))
                nxt[mon] = nxt.get(mon, 0)+x*y
        out = {mon:c for mon,c in nxt.items() if c}
    return out
def coefficient(p, power):
    return {(0,)+mon[1:]:v for mon,v in p.items() if mon[0] == power}
def evaluate(p, values):
    return sum(c*math.prod(v**e for v,e in zip(values, mon)) for mon,c in p.items())

def formal():
    Q,m,K,U,V,h = [variable(i) for i in range(6)]
    one = constant(1)
    q = add(scale(mul(Q,Q),2),scale(Q,-1))
    q2 = mul(q,q)
    zpoly = add(scale(mul(U,add(Q,constant(-1))),2),
                mul(m,add(scale(Q,2),constant(-1)),h))
    P = add(mul(m,add(mul(q2,q2),scale(q2,-1))),
            mul(add(m,scale(U,-1),mul(q,add(m,V))),add(q,constant(-1))),
            scale(mul(add(one,mul(q,K)),add(q2,constant(-1)),zpoly),-1))
    require(max(mon[0] for mon in P)==8, 'formal degree8')
    require(not add(*(coefficient(P,i) for i in range(9))), 'P(1)=0')
    cs = [add(*(coefficient(P,j) for j in range(i+1,9))) for i in range(8)]
    rebuilt = mul(add(Q,constant(-1)),add(*(mul(c,mul(*([Q]*i))) for i,c in enumerate(cs))))
    require(rebuilt==P, 'whole polynomial quotient')
    raw = [U,scale(add(scale(mul(K,U),2),scale(U,2),V),-1),
           add(scale(mul(K,U),4),scale(U,-2)),
           add(scale(mul(K,U),2),scale(U,8),scale(V,4)),
           add(scale(mul(K,U),-12),scale(U,-8)),
           scale(mul(K,U),24),scale(mul(K,U),-16),{}]
    for i,c in enumerate(cs):
        require({mon:v for mon,v in c.items() if mon[1]==0}==raw[i], 'residue coefficient '+str(i))
    require(cs[7]==scale(m,16), 'top coefficient')
    require(cs[6]==add(scale(m,-16),scale(mul(K,U),-16),scale(mul(K,m,h),-16)), 'next coefficient')
    record = {'variables':['Q','m','K','U','V','h'], 'P_terms':len(P),
              'quotient_coefficient_terms':[len(c) for c in cs],
              'all_eight_residue_coefficients':True, 'whole_quotient_identity':True,
              'polynomial_sha256':sha(canonical([[list(k),v] for k,v in sorted(P.items())]))}
    return cs, record

def cyclic_checks():
    pairs = multiples = 0
    for d in range(2,9):
        m = (1<<d)-1
        for x in range(m):
            require(((2*x)%m).bit_count()==x.bit_count(), 'cyclic rotation')
            if x:
                require(((-x)%m).bit_count()==d-x.bit_count(), 'cyclic complement')
            for y in range(m):
                require(((x+y)%m).bit_count()<=x.bit_count()+y.bit_count(), 'cyclic subadditivity')
                pairs += 1
        for k in range(1,257):
            require((m*k).bit_count()>=d, 'positive Mersenne multiple')
            multiples += 1
    return {'subadditivity_pairs':pairs,'positive_multiple_cases':multiples}

def census_checks():
    cases = 0
    for a in range(1,9):
        for k in range(2,19):
            for slack in (0,1,7):
                M = k+15*a+slack
                e = M-6*a+4
                bound = 28*k+18*a+14
                require(e<=M-2 and bound<28*M, 'literal count inequalities')
                require(2*bound*e+2*e<71*M*M, 'actual sufficient margin')
                cases += 1
    return {'scalar_count_cases':cases, 'compiler_tables_constructed':0}

def digit_cases(cs):
    records = []
    theorem_passes = normalizations = zero_residues = max_bits = 0
    for d in (64,125):
        B = 1<<d
        m = B-1
        for positions in ((0,), (0,7), (0,7,13,21)):
            U = sum(1<<j for j in positions)
            V = sum(1<<(2+9*j) for j in range(len(positions)))
            for K in (1<<(d-1), B+(1<<5), 8*B+(1<<4)+(1<<11)):
                e, kap = U.bit_count(), K.bit_count()
                gamma = d-2*kap*e-2*e
                require(gamma>0 and V.bit_count()==e, 'synthetic sparse-mask hypothesis')
                for n in (5,9,17,33):
                    D = d*n
                    Q = 1<<D
                    rep = (Q-1)//m
                    q = Q*(2*Q-1)
                    for h in (1,5,n*n,(1<<math.isqrt(D))+1):
                        z = 2*U*rep+(2*Q-1)*h
                        F = K*z
                        J = (q-1)//m
                        R = (q*q-z-q*F)*(q*q-1)+(m-U+q*(m+V))*J
                        c = [evaluate(p,[0,m,K,U,V,h]) for p in cs]
                        require(R==rep*sum(v*Q**i for i,v in enumerate(c)), 'literal minus source/quotient equality')
                        require((R+1)%(2*Q-1)==0 and z%4==1 and R%4==3, 'resonance and source parity')
                        aa, CC = zip(*(divmod(v,m) for v in c))
                        T = (2*K*U)%m
                        Cwanted = [U,(-T-2*U-V)%m,(2*T-2*U)%m,
                                   (T+8*U+4*V)%m,(-6*T-8*U)%m,(12*T)%m,(-8*T)%m,0]
                        require(list(CC)==Cwanted, 'eight evaluated residues')
                        require(T and (T+2*U+V)%m and (6*T+8*U)%m, 'three nonzero residues')
                        W = sum(v.bit_count() for v in CC[:7])
                        require(W+d>=3*d+gamma, 'joint population bound')
                        H = 3+2*max(abs(v) for v in aa)
                        ell = 2
                        while not H < B**(ell-1):
                            ell += 1
                        if n>=ell+1:
                            carry = 0
                            for i in range(8):
                                eps = (aa[i-1] if i else 0)-aa[i]
                                carry,digit = divmod(CC[i]*rep+eps+carry,Q)
                                actual = (R//Q**i)%Q
                                require(digit==actual and carry in (-1,0), 'all eight normalized blocks')
                                if CC[i]:
                                    require(digit//B**ell==CC[i]*(B**(n-ell)-1)//m, 'all periodic interior digits')
                                else:
                                    zero_residues += 1
                                normalizations += 1
                            require(R//Q**8==15, 'top digit')
                            require(R.bit_count()>=(n-ell)*(W+d), 'whole population lower bound')
                            if gamma*n>=ell*(3*d+gamma)+2:
                                require(R.bit_count()>=3*D+2, 'binary theorem threshold')
                                theorem_passes += 1
                        records.append([d,len(positions),K,n,h.bit_length(),ell,W,R.bit_count()])
                        max_bits = max(max_bits,R.bit_length())
    return {'cases':len(records),'normalized_blocks':normalizations,
            'zero_residue_blocks':zero_residues,'explicit_threshold_passes':theorem_passes,
            'maximum_R_bits':max_bits,'records_sha256':sha(canonical(records)),
            'scope':'relaxed fixed scalar masks satisfying the proved sparse-mask criterion; no compiled machine'}

def source_bindings(data):
    packet = json.loads(data)['packet']
    rows = packet['source']
    require(len(rows)==83 and len(packet['witnesses'])==18, 'unchanged source interface')
    selected = {
      'repunit':['*','Bm1','Jrep'], 'q':['+','repunit',1],
      'Lbig':['*','q','q'], 'q_minus_F':['-','q','F'],
      'q_minus_FZ':['-','q_minus_F','Z'],
      'gap_product':['*','repunit','q_minus_F'], 'gap':['+','gap_product','q_minus_FZ'],
      'Lm1':['-','Lbig',1], 'rproduct':['*','gap','Lm1'],
      'qMF':['*','q','MF'], 'mask_factor':['+','MC','qMF'],
      'mask':['*','mask_factor','Jrep'], 'r_lhs':['+','rproduct','mask'],
      'C_after_alpha':['-','q_minus_FZ','alpha'],
      'scaled_t':['*','twice_cell_bits','x'], 'marked_rhs':['-','C_after_alpha','scaled_t'],
      'W':['-','marked_rhs','Z'], 'odd_index':['+','scaled_t','inner_bits'],
      'kinner':['+','Kconstant','w'], 'innerC':['*','kinner','marked_rhs'],
      'transport_partial':['+','innerC','q_minus_F'],
      'local_rhs':['*','transport_quotient','repunit'],
      'norm_transport':['-','transport_partial','local_rhs'],
    }
    actual = {r[0]:r[1:] for r in rows}
    require(all(actual.get(k)==v for k,v in selected.items()), 'literal outer bindings')
    return {'complete_rows':83,'witnesses':18,'literal_bindings':selected,'array_evaluated':False}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--papers',type=Path,required=True)
    ap.add_argument('--write',type=Path)
    ap.add_argument('--expect',type=Path)
    args = ap.parse_args()
    deps,raws = [],{}
    for name,pin in PINS.items():
        options = [args.root/name, args.papers/'1980'/name,
                   args.papers/'research-wip/native-stream-queue'/name]
        path = next((p for p in options if p.is_file()),None)
        require(path is not None, 'missing '+name)
        raw = path.read_bytes()
        require(sha(raw)==pin, 'pin '+name)
        raws[name]=raw
        deps.append({'name':name,'bytes':len(raw),'sha256':pin})
    cs,formal_record = formal()
    out = {'schema':'resonant minus binary completion v1','status':'PASS',
           'source_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
           'formal':formal_record,'cyclic':cyclic_checks(),'census':census_checks(),
           'digits':digit_cases(cs),'source':source_bindings(raws['complete83_shared_projection_scout.json']),
           'scope':{'actual_compiler_examples':0,'huge_Pell_tuples_materialized':0,
                    'source_DAG_executed':False,'predecessor_execution':False,
                    'all_size_minus_binary_theorem':'proved in companion; evidence corroborates',
                    'new_gate_saving':False}}
    encoded=(json.dumps(out,sort_keys=True,indent=2)+'\n').encode()
    if args.write:
        args.write.write_bytes(encoded)
    if args.expect:
        require(args.expect.read_bytes()==encoded,'exact replay')
    print(json.dumps({'status':'PASS','receipt_sha256':sha(encoded),
                      'digit_cases':out['digits']['cases'],
                      'threshold_passes':out['digits']['explicit_threshold_passes']},sort_keys=True))

if __name__=='__main__':
    main()
