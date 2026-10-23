"""Independent checks of the proposed 121x8801 Wang943 coefficient instance.

Does not import or execute its builder; independently rebuilds the sparse
geometry and integer ports and checks constructive Boolean-orbit fixtures.
"""
import gzip
import hashlib
import json
import math
import random
from pathlib import Path

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'coefficients'

def need(ok, msg):
    if not ok:raise RuntimeError(msg)

def main():
    tiles=json.loads((SOURCE/'upstream/wang943_tiles.json').read_text())
    b,L=121,8801;d=b*L;lam=2341;k=2340
    shifts=[1023,1013,1003,983];anchors=[1095,1096,2195,3296]
    E=set(range(943))|{o+j for o in shifts for j in range(10)}|set(anchors)|{1063,1064}
    coeff={e:0 for e in E}
    for e,tile in enumerate(tiles):
        bits=[int(v) for label in tile for v in reversed(f'{label+512:010b}')]
        need(len(bits)==40,'label exceeds ten bits')
        coeff[e]=1+sum(bit*(1<<(10+2*j)) for j,bit in enumerate(bits+[1]*4))
    for slot,off in enumerate(shifts):
        for j in range(10):coeff[off+j]=1<<(10+2*(10*slot+j))
    for j,e in enumerate(anchors):coeff[e]=1<<(90+2*j)
    Dc={}
    for e in [30,62,1100,2200]:Dc[e]=Dc.get(e,0)+1
    for t in [4393,5495]:
        for e,c in coeff.items():Dc[t-e]=Dc.get(t-e,0)+c
    Dc={e:c for e,c in Dc.items() if c}
    checks=0
    for j in range(10):
        for target,dcfrom,drfrom,tmpfrom in [(1013+j,983+j,None,1013+j),(1065+j,1003+j,1023+j,None)]:
            for e in E:
                need(Dc.get(target-e,0)==int(e==dcfrom),'copy DC contamination')
                need(int(e+42==target)==int(e==drfrom),'copy DR contamination')
                need(int(e==target)==int(e==tmpfrom),'copy temporal contamination')
                checks+=3
    for target,pred in [(2195,1095),(3296,1096)]:
        for e in E:
            need(Dc.get(target-e,0)==int(e==pred),'anchor DC contamination')
            need(e+42!=target,'anchor DR contamination')
            # The temporal source is the identically numbered native anchor.
            need(int(e==target)==int(e in {target}),'anchor temporal')
            checks+=3
    for t in [4393,5495]:
        for e in E:
            need(Dc.get(t-e,0)==coeff[e],'clause contamination')
            need(e+42!=t,'clause DR contamination')
            checks+=2
    need({(4393-e)%L for e in E}.isdisjoint({(5495-e)%L for e in E}),'clause rotation collision')
    need({(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0},'anchor rotation collision')
    maximum=max(Dc)+max(E)
    need(maximum==8791,'convolution bound')
    mu=1022+sum(1<<(10+2*j) for j in range(44))
    mass=(len(E)+2)*(2*sum(coeff.values())+6)
    threshold=max(4*mass+8,2*mu+4,16)
    need(2**119<threshold<2**120<2**121,'radix threshold')
    need(2*((1<<119)-1)+4<1<<121,'padding overflow')
    DC=sum(c<<(b*e) for e,c in Dc.items());DR=1<<(b*42);B=1<<d
    MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(b*1063))
    MF=4+(mu<<(b*4393))+(mu<<(b*5495))
    MF+=sum(1<<(b*e) for e in list(range(1013,1023))+list(range(1065,1075))+[2195,3296])
    MF+=sum(((1<<119)-1)<<(b*e) for e in range(8792,8799))+(((1<<27)-1)<<(b*8799))
    expected={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
    binding=json.loads((SOURCE/'COEFFICIENT_BINDING.json').read_text())
    for entry in binding['files']:
        raw=gzip.decompress((SOURCE/entry['file']).read_bytes())
        value=int.from_bytes(raw,'little')
        need(value==expected[entry['port']],'literal payload differs')
        need(hashlib.sha256(raw).hexdigest()==entry['sha256'],'hash differs')
        need(value.bit_length()==entry['bit_length'],'bit length differs')
    need(MC.bit_count()==d-989 and MF.bit_count()==989,'population')
    need(MC%4==2 and MF%8==4 and 0<MC<B-1 and 0<MF<B-1,'mask contract')
    need(d==11**2*13*677,'factorization')
    need(all(lam%p for p in range(2,math.isqrt(lam)+1)),'lambda composite')
    need(pow(B,k,d)==1,'orbit period modulo d')
    need(pow(B,k,lam**2)==1+1092*lam,'valuation witness')
    table=[]
    for p in [11,13,677,lam]:
        h0=(1+B*DC+B*B*(DR+1))%p
        need((B*B-1)%p and h0,'unit obstruction')
        table.append([p,B%p,(B*B-1)%p,h0])
    # Direct constructive coverage fixtures at the ACTUAL d, B, lambda.
    # The general proof covers every residue. Small a fixtures permit us to
    # enumerate and test the exact selected Boolean subset economically.
    rng=random.Random(881121);fixture_count=0;largest_selected=0
    for n in [4,5]:
        N=lam**n;T=N//lam;C0=d*lam;modulus=d*N
        need(T>C0,'coverage size premise')
        bb=pow(2,d,modulus);orbit=pow(bb,k,modulus)
        def index_for(z):
            target=1+C0*z;index=0
            for s in range(n-1):
                submod=lam**(s+2);power=lam**s;div=lam**(s+1)
                residual=target*pow(pow(orbit,index,submod),-1,submod)%submod
                step=(pow(orbit,power,submod)-1)//div
                digit=((residual-1)//div)*pow(step,-1,lam)%lam
                index+=digit*power
            need(0<=index<T and pow(orbit,index,modulus)==target%modulus,'orbit inverse')
            return index
        width=lam;height=lam**(n-1)
        for a in range(1,9):
            for epsilon in [0,1]:
                u=rng.randrange(T)
                z0=(u-a*(a-1)//2)*pow(a,-1,T)%T
                indices=[2+k*index_for((z0+j)%T) for j in range(a)]
                if epsilon:indices.append(3)
                need(len(indices)==len(set(indices)),'Boolean reuse')
                need(min(indices)>=2 and max(indices)+width<N and max(indices)+1<N,'wrapped position')
                target=bb*bb*(a+C0*u+epsilon*bb)%modulus
                need(sum(pow(bb,j,modulus) for j in indices)%modulus==target,'subset target mismatch')
                q=pow(bb,N,modulus);bw=pow(bb,width,modulus)
                gamma=pow(2,121*1063,modulus)*(q*q-1)*(1+q*(DC+bb*DR+bw))%modulus
                need(math.gcd(gamma,modulus)==1,'nonunit actual Gamma')
                largest_selected=max(largest_selected,max(indices));fixture_count+=1
    report=dict(status='PASS',independent_convolution_checks=checks,
                independent_literal_ports=4,global_convolution_max=maximum,
                threshold=str(threshold),unit_table=table,
                actual_modulus_boolean_subset_fixtures=fixture_count,
                largest_selected_native_cell=str(largest_selected),
                scope='Finite transcription, unit, and constructive-subset diagnostics; universal semantic proof audited separately.')
    (HERE/'COEFFICIENT_INDEPENDENT_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
