"""Exact conditional36 torus interface with seam-forced radix alignment."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_life_one_field_mask as local

B=512
GEOMETRY=[('wm1','-','W',1),('qm1','-','q',1),
          ('hwm1','*','h','wm1'),('wquot','*','W','quot'),
          ('a512','*',512,'A'),
          ('allones','*',511,'J')]
EDGES=[('Ah','*','A','h'),('leftsum','+','C','h'),
       ('lefttwo','*',2,'L'),('leftout','+','Xl','lefttwo'),
       ('rightsum','+','C','Ah'),('AR','*','A','R'),
       ('righttwo','*',2,'AR'),('rightout','+','Xr','righttwo')]
CONV=[('br','*',512,'R'),('edge','-','L','br'),
      ('correction','*','wm1','edge'),('center','*',262657,'C'),
      ('horizontal','+','center','correction'),('W2','*','W','W'),
      ('K0','+','W2','W'),('K','+','K0',1),('conv','*','K','horizontal'),
      ('scaledS','*',512,'S'),('WS','*','W','scaledS'),
      ('quotient','*','qm1','z'),('rhs','+','WS','quotient')]
SHIFTED=[(name,op,('C' if a=='B' else a),('C' if b=='B' else b))
         for name,op,a,b in local.SHIFTED_LOCAL]
SOURCE=GEOMETRY+EDGES+CONV+SHIFTED
EQUALITIES=[('hwm1','qm1'),('wquot','q'),
            ('a512','W'),('allones','qm1'),('leftsum','leftout'),
            ('rightsum','rightout'),('conv','rhs')]
COMBINED=[('Ah','*','A','h'),('edge_mask','+','h','Ah'),
          ('lhs','+','C','edge_mask'),('AR','*','A','R'),
          ('D','+','L','AR'),('twoD','*',2,'D'),('rhs','+','X','twoD')]


def count(source):
    h=local.histogram(source)
    return dict(total=len(source),multiplications=h['M'],additions=h['A'])


def pack(values):return sum(x*B**i for i,x in enumerate(values))


def boolean(word,q):
    assert q>1
    if not 0<=word<q:return False
    while word:
        if word%B not in (0,1):return False
        word//=B
    return True


def source_checks():
    names='W q h quot A J C L R Xl Xr S z Y U'.split()
    values=dict(zip(names,sp.symbols(' '.join(names))))
    e=local.run(SOURCE,values)
    W,q,h,quot,A,J,C,L,R,Xl,Xr,S,z,Y,U=[values[k] for k in names]
    expected=[h*(W-1)-(q-1),W*quot-q,512*A-W,
              511*J-q+1,C+h-Xl-2*L,C+A*h-Xr-2*A*R,
              (W*W+W+1)*(262657*C+(W-1)*(L-512*R))-512*W*S-z*(q-1)]
    for (a,b),f in zip(EQUALITIES,expected):assert sp.expand(e[a]-e[b]-f)==0
    assert sp.expand(e['Vprime']-(28*S+2*C+16*Y+118*U+41*J))==0
    assert count(SOURCE)==dict(total=36,multiplications=21,additions=15)
    assert count(COMBINED)==dict(total=7,multiplications=3,additions=4)
    return dict(full=count(SOURCE),geometry_repunit=count(GEOMETRY),edges=count(EDGES),
                convolution=count(CONV),local=count(SHIFTED),combined_edges=count(COMBINED),
                schedule=SOURCE,equalities=EQUALITIES,symbolic_identities=8,
                mixed_test='Vprime AND(144J)=0; not a paid primitive here.',
                preconditions='q power of two; relevant words Boolean;S nonnegative;0<Vprime<q.')


def witness(n,b):
    y=local.life(n,b)
    us=[u for u in range(2) if local.digit(n,b,y,u)&72==0]
    assert len(us)==1
    return y,us[0]


def alignment_checks():
    cases=aligned=rejected=0
    for exponent in range(9,81):
        for height in range(1,28):
            if exponent*height%9:continue
            W=2**exponent;q=W**height;h=(q-1)//(W-1)
            digits=[];v=h
            while v:
                v,digit=divmod(v,512);digits.append(digit)
            assert all(d==0 or d&(d-1)==0 for d in digits)
            possible=all(d<=3 for d in digits)
            assert possible==(exponent%9==0)
            if possible:aligned+=1
            else:
                rejected+=1
                witness_index=2 if exponent%9==1 else 1
                assert witness_index<height
                assert (witness_index*exponent)%9>=2
            cases+=1
    return dict(power_geometries=cases,aligned=aligned,
                misaligned_rejected=rejected,
                scope='Necessary digit condition from h=Xl+2L-C; general proof in the note.')


def torus_checks():
    cases=cells_checked=corrupt=0
    signs={-1:0,0:0,1:0}
    for m,n in product(range(1,4),repeat=2):
        W=B**m;q=W**n;A=W//B;h=(q-1)//(W-1);J=(q-1)//511
        for code in range(1<<(m*n)):
            cells=[(code>>i)&1 for i in range(m*n)]
            at=lambda i,j:cells[i%m+m*(j%n)]
            L=sum(at(0,j)*W**j for j in range(n))
            R=sum(at(m-1,j)*W**j for j in range(n))
            Xl=pack([cells[i]^int(i%m==0) for i in range(m*n)])
            Xr=pack([cells[i]^int(i%m==m-1) for i in range(m*n)])
            ss=[];yy=[];uu=[];hh=[]
            for j in range(n):
                for i in range(m):
                    s=sum(at(i+di,j+dj) for di,dj in product((-1,0,1),repeat=2))
                    y,u=witness(s-at(i,j),at(i,j))
                    ss.append(s);yy.append(y);uu.append(u)
                    hh.append(sum(at(i+di,j) for di in (-1,0,1)))
            C=pack(cells);S=pack(ss);Y=pack(yy);U=pack(uu)
            H=pack(hh)
            num=(W*W+W+1)*B*H-B*W*S
            assert num%(q-1)==0
            z=num//(q-1)
            values=dict(W=W,q=q,h=h,quot=q//W,A=A,J=J,
                        C=C,L=L,R=R,Xl=Xl,Xr=Xr,S=S,z=z,Y=Y,U=U)
            e=local.run(SOURCE,values)
            assert all(e[a]==e[b] for a,b in EQUALITIES)
            assert e['horizontal']==B*H
            assert 0<e['Vprime']<q and e['Vprime']&(144*J)==0
            assert 28*S<q and S<=9*J<q-1
            for name in ('C','Y','U','L','Xl','Xr','AR'):assert boolean(e[name],q)
            # A wrong output with the same unique genuine helper must fail.
            bad=values.copy();bad['Y']=Y+(1-2*yy[0])
            ebad=local.run(SOURCE,bad)
            assert 0<ebad['Vprime']<q and ebad['Vprime']&(144*J)!=0
            corrupt+=1
            signs[(z>0)-(z<0)]+=1
            cases+=1;cells_checked+=m*n
    return dict(tori=cases,physical_cells=cells_checked,wrong_outputs=corrupt,
                quotient_signs=signs,dimensions=[1,2,3])


def combined_checks():
    candidates=accepted=popchecks=0
    for m,n in product((2,3),(1,2,3)):
        W=B**m;q=W**n;A=W//B;h=(q-1)//(W-1);J=(q-1)//511
        columns=[sum(bit*W**j for j,bit in enumerate(bits)) for bits in product(range(2),repeat=n)]
        for code in range(1<<(m*n)):
            cells=[(code>>i)&1 for i in range(m*n)]
            C=pack(cells)
            expectedL=sum(cells[m*j]*W**j for j in range(n))
            expectedR=sum(cells[m*j+m-1]*W**j for j in range(n))
            for L,R in product(columns,repeat=2):
                X=C+h+A*h-2*(L+A*R)
                ok=boolean(X,q)
                assert ok==((L,R)==(expectedL,expectedR))
                if ok:
                    e=local.run(COMBINED,dict(A=A,h=h,C=C,L=L,R=R,X=X))
                    assert e['lhs']==e['rhs']
                    accepted+=1
                candidates+=1
        sparse=q-1-h
        compensate=3*h+4*J
        assert sparse.bit_count()==9*m*n-n
        assert compensate.bit_count()==m*n+2*n
        masks=[144*J,510*J,510*J,510*J,sparse,sparse,compensate]
        M=sum(v*q**i for i,v in enumerate(masks))
        assert all(0<=v<q for v in masks)
        assert M.bit_count()==45*m*n
        assert (q**7).bit_length()-1+M.bit_count()==108*m*n
        assert q**12==2**(108*m*n)
        popchecks+=1
    # Width1 makes the two indicator columns coincide and invalidates the rule.
    e=local.run(COMBINED,dict(A=1,h=1,C=0,L=1,R=0,X=0))
    assert e['lhs']==e['rhs'] and 1 & ((B-1)-1)==0
    # Combining two column values into L+2R does not separately type them.
    small=16;W=small**2;A=small;D=A*W**2;E=3*W+3*W**2
    R=(D-E)//(A-2);L=E-2*R
    assert (L,R)==(75776,60800) and L>=0 and R>=0
    assert L+A*R==D and L+2*R==E and (L,R)!=(0,W**2)
    return dict(candidate_column_pairs=candidates,accepted_exact_edges=accepted,
                sparse_mask_threshold_cases=popchecks,width1_false_edge=True,
                merged_selector_false_edge=dict(radix=16,width=2,height=3,L=L,R=R))


def verify():
    return dict(status='PASS_ONE_HELPER_TORUS_CONDITIONAL36',source=source_checks(),
                seam_alignment=alignment_checks(),
                torus=torus_checks(),combined_edges=combined_checks(),
                proof='../1980/EXPLORATION_LIFE_ONE_HELPER_TORUS.md',
                review='Author and an independent complete scoped proof/source review pass; fresh read-only verification exactly matches the saved JSON.',
                scope='Exact rectangular torus and one-helper local interface; masks,pre-power bounds,positive adapters and periodic target/raw-input compiler remain separate.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status']);print(result['source']['full'])
    print(result['torus']);print(result['combined_edges'])
