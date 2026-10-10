"""Small exact, all-rational companion proof at weight three."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
from package_io import DATA_DIR, write_json_new_or_compare
from octet import basic,imag,coords,scalar,shuffle_lin,sub,sh,add,octa,ds

def target_s2():
    out=Counter({(0,-2,-2):12,(0,-2,2):4})
    P={(2,):1,(-2,):-1};P3={():1}
    for j in range(3):P3=shuffle_lin(P3,P)
    for w,c in P3.items():add(out,w,c)
    out=sub(out,scalar(sh((0,-2),(-1,)),8))
    return imag(out)

def find(output=None):
    keys=coords(3);idx={w:i for i,w in enumerate(keys)}
    rows=list(basic(3));basis={};trans={};target={idx[w]:Q(c) for w,c in target_s2().items()}
    for ix,(label,raw) in enumerate(rows):
        r={idx[w]:Q(c) for w,c in imag(raw).items()};coef={ix:Q(1)}
        while r:
            k=min(r);a=r[k]
            if k in basis:
                for j,c in basis[k].items():
                    r[j]=r.get(j,Q(0))-a*c
                    if not r[j]:del r[j]
                for j,c in trans[k].items():
                    coef[j]=coef.get(j,Q(0))-a*c
                    if not coef[j]:del coef[j]
            else:
                basis[k]={j:c/a for j,c in r.items()};trans[k]={j:c/a for j,c in coef.items()};break
        r=target.copy();solution=Counter()
        while r:
            k=min(r)
            if k not in basis:break
            a=r[k]
            for j,c in basis[k].items():
                r[j]=r.get(j,Q(0))-a*c
                if not r[j]:del r[j]
            for j,c in trans[k].items():add(solution,j,a*c)
        if not r:
            out=Counter()
            cert=[]
            for j,c in solution.items():
                if not c:continue
                tag,raw=rows[j]
                cert.append({'label':tag,'coefficient':str(c)})
                for w,v in imag(raw).items():add(out,w,c*v)
            assert out==target_s2()
            data={'identity':'S2 = -2 g21 + pi^3/32 - 2 G log(2)','rows':cert,'weight':3,'target_multiplier':4}
            if output is not None:write_json_new_or_compare(output,data)
            print('EXACT S2 CERTIFICATE',len(cert),'rows; rank',len(basis))
            for item in cert:print(item)
            return data
    raise RuntimeError('S2 target not spanned')

def verify():
    data=json.loads((DATA_DIR/'s2_exact_certificate.json').read_text());out=Counter()
    for item in data['rows']:
        tag=item['label'];c=Q(item['coefficient'])
        if tag[0]=='ds':
            assert len(tag[1])+len(tag[2])==3
            row=ds(tuple(tag[1]),tuple(tag[2]))
        elif tag[0]=='octa':
            assert len(tag[1])==3
            row=octa(tuple(tag[1]))
        else:raise ValueError(tag)
        for w,v in imag(row).items():add(out,w,c*v)
    assert out==target_s2()
    print('PASS: exact S2 companion certificate')
    return {'weight':3,'rows':len(data['rows']),'exact_target_verified':True}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild',action='store_true',help='Re-run the small exact search and compare the certificate')
    args=parser.parse_args()
    if args.rebuild:
        assert find()==json.loads((DATA_DIR/'s2_exact_certificate.json').read_text()), 'Rebuilt certificate differs'
    verify()
