#!/usr/bin/env python3
"""Independent decoder/audit of the four raw coefficient payloads.
Does not import or execute a generator. Standard library only.
"""
from pathlib import Path
import json,hashlib,gzip,math,sys,argparse
H=Path(__file__).resolve().parent

def check(x,label):
    if not x:raise ValueError(label)
def digest(x):return hashlib.sha256(x).hexdigest()
def primes_to(n):return [p for p in range(2,n+1) if all(p%a for a in range(2,math.isqrt(p)+1))]
def run(folder):
    binding=json.loads((folder/'COEFFICIENT_BINDING.json').read_text()); values={}
    for name in ('beta','K','MC','MF_source'):
        raw=(folder/(name+'.bin')).read_bytes(); gz=(folder/(name+'.bin.gz')).read_bytes();m=binding['payloads'][name]
        check(digest(raw)==m['sha256'] and digest(gz)==m['gzip_sha256'],'stored hashes')
        check(gzip.decompress(gz)==raw,'gzip recovery')
        value=int.from_bytes(raw,'little');check(value.bit_length()==m['bits'] and len(raw)==m['bytes']==(value.bit_length()+7)//8,'minimal payload');values[name]=value
    d=1064921;b=121;L=8801;B=1<<d;rho=1<<b
    check(values['beta']==B-1,'beta exact')
    DR,DC=divmod(values['K'],B);check(DR==rho,'DR exact')
    MF=values['MF_source']-values['beta'];MC=values['MC']
    tiles=[tuple(t) for t in json.loads((H/'wang943_tiles.json').read_text())]
    rawmachine=(H/'k215.tm').read_bytes();check(digest(rawmachine)=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','literal machine')
    actions={}
    for line in rawmachine.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,s,t,m,r=line.split();key=int(q),int(s);check(key not in actions,'unique action');actions[key]=(int(t),m,int(r))
    check(set(actions)=={(q,b) for q in range(215) for b in range(2)},'full action domain')
    rs=sorted({v[2] for v in actions.values() if v[1]=='R'});ls=sorted({v[2] for v in actions.values() if v[1]=='L'})
    right={q:6+i for i,q in enumerate(rs)};left={q:205+i for i,q in enumerate(ls)};head=lambda q,s:2*(q+1)+s
    expected=[]
    for (q,s),(t,m,r) in sorted(actions.items()):
        expected.append((0,head(q,s),right[r],t) if m=='R' else (left[r],head(q,s),0,t))
    expected.extend((0,head(215,s),0,head(215,s)) for s in range(2))
    expected.extend((0,s,0,s) for s in range(2))
    for q,signal in right.items():expected.extend((signal,s,0,head(q,s)) for s in range(2))
    for q,signal in left.items():expected.extend((0,s,signal,head(q,s)) for s in range(2))
    expected.extend((0,x,0,438) for x in (0,1,432,433))
    expected.extend([(2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)])
    expected.extend((1,438,1,x) for x in (434,435,436))
    expected.extend((a,437,z,437) for a in (0,1,4) for z in (0,1,2));expected.append((5,0,0,0))
    check(len(expected)==len(set(expected))==len(tiles)==943,'tile multiplicity')
    check(tiles==[(2,435,3,1),(5,0,0,0)]+sorted(set(expected)-{(2,435,3,1),(5,0,0,0)}),'ordered language')
    native=list(range(943))+[o+2*j for o in (1020,1000,980,960) for j in range(10)]+[1063,1064,1095,1096,2195,3296]
    check(len(set(native))==989,'support distinct')
    missing=(B-1)-MC
    expectedmissing=sum(1<<(b*e) for e in native if e!=1)+(1<<(b*1063+1))
    check(missing==expectedmissing,'complete low mask')
    # Decode all radix digits from actual DC, with no generator map.
    dc_digits=[];temp=DC
    while temp:
        dc_digits.append(temp&(rho-1));temp>>=b
    def actual(e):return dc_digits[e] if 0<=e<len(dc_digits) else 0
    weights=[4**j*1024 for j in range(44)]
    clauses={i:1+sum(weights[10*t+j] for t,x in enumerate(tile) for j in range(10) if (x+512)&(1<<j))+sum(weights[40:]) for i,tile in enumerate(tiles)}
    for t,offset in enumerate((1020,1000,980,960)):
        for j in range(10):clauses[offset+2*j]=weights[t*10+j]
    clauses.update(dict(zip((1095,1096,2195,3296),weights[40:])));clauses.update({1063:0,1064:0})
    for exponent in range(L):
        expectedvalue=int(exponent in (40,41,1100,2200))+sum(clauses.get(t-exponent,0) for t in (4393,5495))
        check(actual(exponent)==expectedvalue,'full DC coefficient decode')
    mu=1022+sum(weights)
    maskwords={0:4,4393:mu,5495:mu,2195:1,3296:1,8799:(1<<27)-1}
    maskwords.update({8792+i:(1<<119)-1 for i in range(7)})
    for j in range(10):maskwords[1000+2*j]=1;maskwords[1021+2*j]=1
    check(MF==sum(v<<(b*e) for e,v in maskwords.items()),'entire high mask')
    check((MC.bit_count(),MF.bit_count(),MC%4,MF%8)==(d-989,989,2,4),'actual populations/residues')
    check(0<MC<B-1 and 0<MF<B-1 and DC<B,'native bounds')
    count=0
    ts=[(1000+2*j,960+2*j,None,1000+2*j) for j in range(10)]+[(1021+2*j,980+2*j,1020+2*j,None) for j in range(10)]+[(2195,1095,None,2195),(3296,1096,None,3296)]
    for t,a,r,y in ts:
        for e in native:
            check(actual(t-e)==int(e==a),'basis dc');check(int(e+1==t)==int(e==r),'basis dr');check(int(e==t)==int(e==y),'basis temporal');count+=3
    for t in(4393,5495):
        for e in native:check(actual(t-e)==clauses[e] and e+1!=t,'clause basis');count+=2
    check(not ({(4393-e)%L for e in native}&{(5495-e)%L for e in native}),'clean clauses')
    check({(2195-e)%L for e in native}&{(3296-e)%L for e in native}=={0},'unique anchor rotation')
    mass=991*(2*sum(clauses.values())+6)
    check(4*mass+8<rho and 2*mu+4<rho and 2*((1<<119)-1)+4<rho,'uniform carry')
    check(3*rho//4+mass<=rho-2 and rho//2+1+mass<=rho-2,'strict slack')
    check(len(dc_digits)-1+max(native)==8791<8792 and 8799<L,'external zero region')
    check([n for n in range(944) if not(n&1022)]==[0,1],'mixed count decoding')
    check([(x,y) for x in (0,1) for y in (0,1) if not((x+y)&1)]==[(0,0),(1,1)],'payload decoding')
    check(d==121*13*677,'d factors')
    for p in(11,13,677,2341):check(all(p%r for r in range(2,math.isqrt(p)+1)),'prime proof')
    exact_orders={}
    for modulus in(121,13,677):
        a=1
        for order in range(1,modulus+1):
            a=a*(B%modulus)%modulus
            if a==1:break
        exact_orders[modulus]=order
    check(exact_orders=={121:10,13:12,677:52},'orders from iteration')
    check(math.lcm(*exact_orders.values())==780 and 2340%780==0,'joint order')
    r=pow(B,2340,2341**2);check(r==2556373 and (r-1)%2341==0 and (r-1)%(2341**2)!=0,'valuation one')
    units={}
    for p in(11,13,677,2341):
        q=B%p;v=(q*q-1)%p;h=(1+q*(DC%p)+q*q*((DR%p)+1))%p
        check(v and h,'actual rank unit');units[str(p)]=[q,v,h]
    # Algebraic coverage step checked independently at small odd test moduli.
    coverage=0
    for ell,Cfixed in((3,5),(5,7),(7,3)):
        C0=Cfixed*ell;T=ell**4
        if T<=C0:continue
        for target in range(C0*T):
            Btest=2
            eps=0 if target%ell else 1
            rem=(target-eps*Btest)%(C0*T);a=rem%C0
            check(1<=a<C0 and math.gcd(a,T)==1,'coverage cardinality')
            u=(rem-a)//C0;z=((u-a*(a-1)//2)*pow(a,-1,T))%T
            total=a+C0*(a*z+a*(a-1)//2)+eps*Btest
            check(total%(C0*T)==target,'coverage algebra');coverage+=1
    return {'status':'PASS','imports_builder':False,'machine_action_count':430,'ordered_tiles':943,'native_basis_checks':count,'full_DC_digits_checked':L,'actual_raw_bytes':sum(binding['payloads'][n]['bytes'] for n in values),'exact_orders':exact_orders,'rank_unit_rows':units,'non_Wieferich_residue':r,'coverage_regressions':coverage,'scope':'Finite hypotheses and independent actual coefficient decoding; universal equivalence supplied by COEFFICIENT_PROOF.md.'}
if __name__=='__main__':
    check(__debug__,'run without optimization')
    ap=argparse.ArgumentParser();ap.add_argument('--payloads',type=Path,default=H/'payloads');a=ap.parse_args();print(json.dumps(run(a.payloads),indent=2))
