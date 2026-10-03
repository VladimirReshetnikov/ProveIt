"""Exact post-kernel strata after deleting the63 FIFO width inequality."""
import argparse
import json
from pathlib import Path
import native_dualrail_fifo63 as prior


def valuation(r):
    result=0;power=3
    while power<=2*r:
        result+=(2*r)//power-2*(r//power)
        power*=3
    return result


def stratum(fields,t):
    q=3**t
    r=sum(F*q**i for i,F in enumerate(fields))
    chunks=[r//q**i%q for i in range(3)]+[r//q**3]
    if chunks!=list(fields):return None
    digits=[];v=r
    while v:
        digits.append(v%3);v//=3
    N=4*t
    if len(digits)==N and digits[0]==2 and all(d in (1,2) for d in digits[1:]):
        return 'short'
    if len(digits)!=N+1 or digits[-1]!=1 or digits[0]!=2:return None
    zeros=[j for j,d in enumerate(digits) if d==0]
    if len(zeros)!=1 or zeros[0] not in (t-1,2*t-1,3*t-1):return None
    j=zeros[0]
    if digits[j+1]!=2:return None
    return f'long{(j+1)//t}'


def scan():
    records=[]
    for t in (1,2,3):
        q=3**t;counts={};checked=postkernel=accepted=0
        for fields in prior.fields_with_joint_bound(q):
            checked+=1
            r=sum(F*q**i for i,F in enumerate(fields))
            if r%2:continue
            kind=stratum(fields,t)
            assert (valuation(r)>=4*t)==(kind is not None),(t,fields,r,kind)
            if kind is None:continue
            postkernel+=1
            A=fields[0]+fields[1]-q+1;D=fields[2]+fields[3]-q+1
            for m in range(t+1):
                W=3**m;I=D-W*A
                if I<6 or I%6:continue
                accepted+=1
                assert t>=2 and A!=0
                if A<0:assert kind in ('long1','long2') and q<=D<I
                else:
                    assert kind in ('short','long3')
                    assert kind=='short' or W==1
                    if kind=='long3':assert D>=q-q//3+1 and I>q//3+2 and q<3*I
                if W>=3:assert kind!='long3'
                counts[kind]=counts.get(kind,0)+1
        records.append(dict(t=t,positive_field_tuples=checked,even_valuation_admitted=postkernel,
                            positive_input_width_tuples=accepted,strata=counts))
    return records


def examples():
    examples=[dict(q=9,W=9,x=3,fields=[2,5,4,13],expected='long1'),
              dict(q=9,W=1,x=1,fields=[5,4,1,14],expected='long3'),
              dict(q=27,W=3,x=1,fields=[14,13,22,13],expected='short')]
    result=[]
    for row in examples:
        q,W,x,F=row['q'],row['W'],row['x'],row['fields']
        t=2 if q==9 else 3
        r=sum(f*q**j for j,f in enumerate(F));A=F[0]+F[1]-q+1;D=F[2]+F[3]-q+1
        assert D==6*x+W*A and A+D<q and r%2==0 and valuation(r)==4*t
        assert stratum(F,t)==row['expected']
        result.append(dict(row,r=r,A=A,D=D,alpha=q-A-D,L=q//W))
    return result


def negative_family():
    for t in range(2,13):
        q=3**t;H=(q-1)//2;F=(H+1-q//3,H+1,H,q+H)
        r=sum(f*q**j for j,f in enumerate(F));A=2-q//3;D=q;W=9;x=2*q//3-3
        assert min(F)>0 and x>0 and D==6*x+W*A and q-A-D==q//3-2>0
        assert r%2==0 and valuation(r)==4*t and stratum(F,t)=='long1'
    return dict(checked_t=[2,12],formula='q=3^t,W=9,x=2q/3-3,F=(H+1-q/3,H+1,H,q+H)',
                scope='Parametrically proved full weakened-source family using the positive Pell converse')


def verify():
    return dict(status='PASS_WIDTH_DELETED_POST_KERNEL_CLASSIFICATION',scan=scan(),examples=examples(),
                negative_append_family=negative_family(),
                scope='Exact four digit strata, sign classification and positive Pell extension; no universality or decidability theorem claimed',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))
