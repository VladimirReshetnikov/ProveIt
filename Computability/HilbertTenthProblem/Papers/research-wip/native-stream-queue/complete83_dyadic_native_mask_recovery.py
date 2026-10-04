"""Fresh finite evidence for conditional dyadic native-mask recovery.

Only predecessor bytes/JSON are read. No inherited helper, compiler, or source
DAG is evaluated. Synthetic radix examples are not valid compiler instances.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path

PINS={
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'complete83_shared_projection_math.md':'1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
 'complete83_even_radix_boundary.md':'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc',
 'complete83_dyadic_negative_offset_exclusion.md':'9e24c06c8627e50718f0b00236df7dbb83e8ac9701bc3536e097148b3ae922f2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
 '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
 '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
}

def ck(p,msg):
    if not p:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def unique(pairs):
    out={}
    for k,v in pairs:
        ck(k not in out,'duplicate JSON key');out[k]=v
    return out
def v2(n):
    ck(n!=0,'zero valuation');n=abs(n)
    return (n&-n).bit_length()-1

def source(root):
    for name,h in PINS.items():ck(sha((root/name).read_bytes())==h,'pin '+name)
    p=json.loads((root/'complete83_shared_projection_scout.json').read_text(),object_pairs_hook=unique)['packet']
    rs=p['source'];ck(len(rs)==83,'row count')
    ck(Counter(r[1] for r in rs)==Counter({'*':46,'+':20,'-':17}),'ledger')
    known=set(p['free'])
    for name,op,a,b in rs:
        ck(name not in known and all(type(x) is int or x in known for x in (a,b)),'ordered DAG')
        known.add(name)
    rows={r[0]:r for r in rs}
    guards=[
      ['repunit','*','Bm1','Jrep'],['q','+','repunit',1],
      ['wn2','*','w','q'],['sn2','*','s','n2'],['n2','*','Lbig','q'],
      ['scaled_t','*','twice_cell_bits','x'],['odd_index','+','scaled_t','inner_bits'],
      ['marked_rhs','-','C_after_alpha','scaled_t'],['W','-','marked_rhs','Z'],
      ['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
      ['rproduct','*','gap','Lm1'],['r_lhs','+','rproduct','mask'],
      ['mask','*','mask_factor','Jrep'],['mask_factor','+','MC','qMF'],['qMF','*','q','MF'],
      ['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],
      ['transport_partial','+','innerC','q_minus_F'],['local_rhs','*','transport_quotient','repunit'],
      ['norm_transport','-','transport_partial','local_rhs'],
    ]
    for row in guards:ck(rows[row[0]]==row,'literal interface '+row[0])
    ck(len(p['witnesses'])==18 and p['ordinary_input']=='x','positive interface')
    return {'rows':83,'M':46,'A':37,'positive_witnesses':18,'literal_guards':len(guards),'source_evaluated':False}

def valuation_evidence():
    checked=exceptional=0;digest=hashlib.sha256()
    for r in range(25,1024,2):
        cs=[comb(2*r,r+j) for j in range(4)]
        p,k,l,h=r.bit_count(),v2(r+1),v2(r+3),v2(r-1)
        ck([v2(c) for c in cs]==[p,p-k,p+h-k,p+h-k-l],'four adjacent valuations')
        for t in range(4,11):
            for u in range(t+5,t+10):
                if p>=3*t+1:continue
                vals=[v2(cs[j])+j*u for j in range(4)]
                if k==u:
                    ck(vals[0]==vals[1] and min(vals[2:])>p,'exception shape')
                    exceptional+=1;continue
                if k<u:
                    ck(vals[0]<min(vals[1:]),'central unique')
                else:
                    ck(vals[1]<min(vals[0],vals[2],vals[3]),'first unique')
                cubic=sum(cs[j]*(-(1<<u))**j for j in range(4))
                ck(v2(cubic)==min(vals)<3*t+1,'nonexception cannot reach scale')
                digest.update(f'{r},{t},{u},{v2(cubic)}\n'.encode());checked+=1
    # Wide exponent-only families test the carry bound l<=p+1 without giant binomials.
    wide=0
    for t in range(4,41):
        for exponent in range(2,4*t):
            for r in ((1<<exponent)-3,(1<<exponent)-1,3*(1<<exponent)-1):
                if r<3:continue
                p,k,l,h=r.bit_count(),v2(r+1),v2(r+3),v2(r-1)
                for u in (t+5,t+9,2*t+5):
                    if p>=3*t+1 or k==u:continue
                    vals=[p,p-k+u,p+h-k+2*u,p+h-k-l+3*u]
                    ck(min(vals)>=0 and vals.count(min(vals))==1 and min(vals)<3*t+1,'wide valuation dichotomy')
                    if k==1:ck(l<=p+1 and vals[3]>p,'long third-denominator guard')
                    wide+=1
    return {'exact_binomial_nonexception_cases':checked,'exact_exception_shapes':exceptional,
            'wide_exponent_valuation_cases':wide,'exact_records_sha256':digest.hexdigest()}

def radix_evidence():
    rotations=0;digest=hashlib.sha256()
    for b in (5,7,9):
        V=1<<b
        for L in (7,8,9):
            B=V**L;emax=L-4
            allowed=list(range(2,emax+1))
            for mask in range(1,1<<len(allowed)):
                E=[0]+[e for j,e in enumerate(allowed) if mask>>j&1]
                for star in E[1:]:
                    D=sum(V**e for e in E)+2*V**star
                    ck(D%V==1 and 0<D<B-1,'native synthetic D')
                    # Synthetic positive coefficient strings obey the same scalar
                    # hypotheses; they are not produced by a universal compiler.
                    DC,DR=V**2,V**3
                    raw=(DC+DR)*D
                    digits=[raw//V**j%V for j in range(L)]
                    ck(raw<B and max(digits)<=V//4-2,'synthetic coefficient margin')
                    for shift in range(b*L):
                        rot=pow(2,shift,B-1)*D%(B-1)
                        ds=[rot//V**j%V for j in range(L)]
                        ell=shift%b
                        bound=3*(1<<ell) if ell<=b-2 else V//2+1
                        ck(max(ds)<=bound,'rotation digit bound')
                        plus=raw+rot;actual=plus-V*D
                        ck(0<actual<plus<B-1,'unique positive transport representative')
                        ck(actual%V==rot%V<V-4,'low digit contradiction')
                        ck(max(plus//V**j%V for j in range(L))<=V-2,'no carry margin')
                        digest.update(f'{b},{L},{D},{shift},{actual%V}\n'.encode());rotations+=1
    return {'synthetic_rotation_transport_cases':rotations,'records_sha256':digest.hexdigest(),
            'synthetic_values_claimed_as_compiler_outputs':False}

def build(root):
    return {'source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'interface':source(root),
            'valuation_evidence':valuation_evidence(),'radix_evidence':radix_evidence(),
            'scope':{'assumes_valid_modified_compiler':True,'assumes_q_dyadic_and_W_zero':True,
                     'concludes_exact_population_and_native_masks':True,
                     'proves_two_rotation_synchronization':False,'new_universal_bound':False,
                     'native_or_Pell_zero_materialized':False,'predecessor_program_execution':False}}

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();text=json.dumps(build(a.root),sort_keys=True,indent=2)+'\n'
    if a.output:
        with a.output.open('x') as f:f.write(text)
    else:ck(a.expect.read_text()==text,'exact receipt replay')
    print('PASS: conditional dyadic W-zero typing evidence; no universal bound')

if __name__=='__main__':main()
