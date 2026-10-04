"""Independent arithmetic for the even-radix theorem; no inherited code runs."""
import argparse
import hashlib
import json
from math import comb
from pathlib import Path

AUTHOR_PINS = {
 'py':'b469fb611d4b020fab1cdd5d4946ec1b56d81f1f8682cc3e9a4a7210d9eeef89',
 'json':'68ab9c241c7b8f6e610f1eae697558938630d25b7cdaffff8b17196c9c5fbc0a',
 'md':'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc',
}
SOURCE_PIN = 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c'

def check(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def unique(items):
    out = {}
    for k,v in items:
        check(k not in out, 'duplicate key')
        out[k] = v
    return out

def factorial_v(n,p):
    result = 0
    while n:
        n //= p
        result += n
    return result

def binomial_v(n,k,p):
    return factorial_v(n,p)-factorial_v(k,p)-factorial_v(n-k,p)

def binomial_carries(n,k,p):
    a,b,carry,count=k,n-k,0,0
    while a or b or carry:
        total=a%p+b%p+carry
        carry=total//p
        count+=carry
        a//=p;b//=p
    return count

def build(root, author_root):
    check(set(AUTHOR_PINS) == {'py','json','md'}, 'final author pins required')
    for ext,h in AUTHOR_PINS.items():
        file = author_root / ('complete83_even_radix_boundary.'+ext)
        check(digest(file.read_bytes()) == h, 'author pin '+ext)
    source = root/'complete83_shared_projection_scout.json'
    check(digest(source.read_bytes()) == SOURCE_PIN, 'source pin')
    packet = json.loads(source.read_text(), object_pairs_hook=unique)['packet']
    rows = {r[0]:r for r in packet['source']}
    expected = [
      ['repunit','*','Bm1','Jrep'],['q','+','repunit',1],
      ['wn2','*','w','q'],['sn2','*','s','n2'],['n2','*','Lbig','q'],
      ['marked_rhs','-','C_after_alpha','scaled_t'],['W','-','marked_rhs','Z'],
      ['odd_index','+','scaled_t','inner_bits'],
      ['gap','+','gap_product','q_minus_FZ'],
      ['gap_product','*','repunit','q_minus_F'],
      ['rproduct','*','gap','Lm1'],['r_lhs','+','rproduct','mask'],
      ['mask','*','mask_factor','Jrep'],['mask_factor','+','MC','qMF'],
      ['qMF','*','q','MF'],['gam','*','sigma','a4m5'],
      ['shared_main_partial','+','D1','shared_projection'],
      ['exponent_rhs','+','exponent_partial','shared_projection'],
      ['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],
      ['transport_partial','+','innerC','q_minus_F'],
      ['norm_transport','-','transport_partial','local_rhs'],
    ]
    for row in expected:
        check(rows[row[0]] == row, 'interface '+row[0])
    scalar = dict(Bm1=15,Kconstant=28,twice_cell_bits=8,inner_bits=1,MC=14,MF=19,
                  Jrep=5,x=1,F=6,Z=29,alpha=32)
    q=scalar['Bm1']*scalar['Jrep']+1
    C=q-scalar['F']-scalar['Z']-scalar['alpha']-scalar['twice_cell_bits']*scalar['x']
    W=C-scalar['Z']; u=scalar['twice_cell_bits']*scalar['x']+scalar['inner_bits']
    R=(q*q-scalar['Z']-q*scalar['F'])*(q*q-1)+(scalar['MC']+q*scalar['MF'])*scalar['Jrep']
    r=(R-1)//2
    check((q,C,W,u,R,r)==(76,1,-28,9,30562815,15281407),'outer values')
    offset=(1<<u)-W
    check(offset==540 and R%4==3 and 3*q+1<R<q**4-q**3,'outer inequalities')
    check((pow(2,R,q)-offset)%q == 0,'q divides X')
    # Lifting modulo q*(q-1) permits exact division by q without constructing X.
    lift=(pow(2,R,q*(q-1))-offset)%(q*(q-1))
    check(lift%q==0,'residue lift')
    wmod=(lift//q)%(q-1)
    check(wmod==53 and (wmod+97)%75==0,'transport')
    valuations={str(p):[binomial_v(2*r,r+j,p) for j in range(4)] for p in (2,19)}
    check(valuations=={'2':[16,8,9,8],'19':[3,3,3,3]},'independent Legendre valuations')
    carries={str(p):[binomial_carries(2*r,r+j,p) for j in range(4)] for p in (2,19)}
    check(carries==valuations,'independent Kummer carry counts')
    check(all(v>=7 for v in valuations['2']) and all(v>=3 for v in valuations['19']), 'termwise divisibility')
    check(q**4%(2*q**3)==0,'tail divisibility')
    # Independent full scalar sum, evaluated by direct pow/comb rather than Horner.
    cases=0
    records=hashlib.sha256()
    for qr in range(2,33,2):
        modulus=2*qr**3
        for rr in range(3,100,2):
            for w in (1,2,3,5,8):
                xx=qr*w
                full=sum(comb(2*rr,rr+j)*pow(xx,j,modulus) for j in range(rr+1))%modulus
                cubic=sum(comb(2*rr,rr+j)*pow(xx,j,modulus) for j in range(4))%modulus
                check(full==cubic and full%2==0,'full/cubic modular sum')
                records.update(f'{qr},{rr},{w},{full}\n'.encode());cases+=1
    # Small finite corroboration of the parity argument on the literal R expression.
    parity_cases=0
    for B in (2,4,8,16,32):
        for J in range(2,18,2):
            qr=(B-1)*J+1
            for F,Z,MC,MF in ((1,1,2,3),(2,3,14,19),(7,4,5,8)):
                packed=(qr*qr-Z-qr*F)*(qr*qr-1)+(MC+qr*MF)*J
                check(qr%2==1 and packed%2==0,'odd-q packing parity')
                parity_cases+=1
    return {'source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR_PINS,
            'source_pin':SOURCE_PIN,'literal_interface_rows':len(expected),
            'outer':{**scalar,'q':q,'C':C,'W':W,'u':u,'R':R,'r':r,'offset':offset,'w_mod_75':wmod},
            'binomial_valuations':valuations,'independent_Kummer_carries':carries,'full_cubic_modular_cases':cases,
            'modular_records_sha256':records.hexdigest(),'odd_q_parity_cases':parity_cases,
            'scope':{'full_author_text_read':True,'prior_program_execution':False,
                     'full_source_DAG_evaluation':False,'native_or_Pell_zeros_materialized':False,
                     'diagnostic_valid_compiler_claim':False}}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--author-root',type=Path,required=True)
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=ap.parse_args();result=build(a.root,a.author_root)
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.output:
        with a.output.open('x') as f:f.write(text)
    else:check(a.expect.read_text()==text,'exact receipt replay')
    print('PASS: independent even-radix boundary arithmetic and interface')

if __name__=='__main__':main()
