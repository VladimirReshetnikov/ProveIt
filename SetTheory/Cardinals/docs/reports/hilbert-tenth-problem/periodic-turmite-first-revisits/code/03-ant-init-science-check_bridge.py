#!/usr/bin/env python3
"""Independent own-code finite arithmetic checks; no upstream imports/execution."""
if not __debug__: raise RuntimeError('Optimized mode unsupported: checks require assertions')
import hashlib, itertools, json, pathlib, random
from bridge_dag import U,V,DAG,build,closed_cost,strict_cost,chain,build_uniform_wrapper,uniform_wrapper_cost
ROOT=pathlib.Path(__file__).resolve().parent
PIN='cc67f7c924bcb27ca1c4a48c8d3a630d837b639fbff3032d04515ec1d534ed68'

def addterm(poly,e,c):
    poly[e]=poly.get(e,0)+c
    if poly[e]==0:del poly[e]

def horner_coeff(coeff,base):
    ans=0
    for c in reversed(coeff):ans=ans*base+c
    return ans

def periodic_checks():
    rng=random.Random(17440);count=0;boundary=0
    for u,v,a,k in itertools.product([2,4,6],[2,4],[2,3],[1,2]):
        w=1+a*u;h=2*k*v;W=3**w;Q=W**h;H=W**(k*v);G=W**v;wp=W//3
        for trial in range(4):
            tile=[[rng.randrange(2) for _ in range(u)] for _ in range(v)]
            row=[sum(tile[j][i]*3**i for i in range(u)) for j in range(v)]
            first=[tile[j][0] for j in range(v)]
            hx=(wp-1)//(3**u-1);K=(H-1)//(G-1);hy=K*(H+1)
            bg=hy*(hx*horner_coeff(row,W)+wp*horner_coeff(first,W))
            dense=sum(tile[y%v][x%u]*3**(x+w*y) for y in range(h) for x in range(w))
            assert bg==dense and bg<Q
            assert hx>1 and H*H==Q and hy==(Q-1)//(G-1)
            count+=1
        for ww in range(3,28,2):
            quotient,rem=divmod(3**(ww-1)-1,3**u-1)
            assert (rem==0 and quotient>1)==(ww%u==1 and ww>=2*u+1)
            boundary+=1
    return count,boundary

def patch_checks(anchor):
    J={};count=0;max_terms=0
    assert len(anchor)==2806 and len({(a,b) for a,b,old,new in anchor})==2806
    for a,b,old,new in anchor:
        assert old in [0,1] and new==1-old
        assert 0<=b+144<=220 and 0<=289200-a<=583
        addterm(J,289200-a,(new-old)*3**(b+144))
    words=[p for n in range(4) for p in itertools.product([0,1],repeat=n)]
    for ell,r in itertools.product(words,repeat=2):
        m=len(ell)+len(r)+1;n=m-1
        # Closed expression, in W, after factoring Cbase*P.
        formula={}
        for e,c in J.items():addterm(formula,V-550+V*n+e,c)
        Z={23945:1}
        for i,b in enumerate(list(reversed(ell))+[0]+list(r)):
            if b:
                for offset in [263945+24000,263945+264000+24000]:
                    addterm(Z,V*(m-1-i)+offset,1)
        for offset in [263945,263945+264000]:addterm(Z,V*len(r)+offset,1)
        for e,c in Z.items():
            addterm(formula,e,-3**198*c);addterm(formula,e+1,-3**198*c)
        # Independently construct literal coordinate map, including duplicate
        # left-marker write to test its agreeing overlap rather than erase it.
        cells={(a,b):(old,new) for a,b,old,new in anchor}
        def box(module,slot):
            for x in [module*576000+704+24000*slot,module*576000+705+24000*slot]:
                if (x,54) in cells:assert cells[x,54]==(1,0)
                cells[x,54]=(1,0)
        box(0,12);box(m,11)
        for i,s in enumerate(list(reversed(ell))+[2]+list(r)):
            for bit in range(11):
                if (s>>bit)&1:box(i,13+bit);box(i+1,bit)
        assert len(cells)==2812+4*(sum(ell)+sum(r))
        direct={}
        for (a,b),(old,new) in cells.items():
            addterm(direct,V*m+288650-a,(new-old)*3**(b+144))
            x=b-75+U;y=288650-a+V*m
            assert 0<=x<2*U+1 and 0<=y<2*V*m
        assert direct==formula,(ell,r)
        assert min(direct)>=0
        max_terms=max(max_terms,len(direct));count+=1
    return {'word_pairs':count,'anchor_coefficients_nonzero':len(J),'max_sparse_polynomial_terms':max_terms,'anchor_signed_color_sum':sum(new-old for a,b,old,new in anchor)}

def raw_checks():
    count=0
    for length in range(7):
        codes=[]
        for bits in itertools.product([0,1],repeat=length):
            a=1
            for b in bits:a=2*a+b
            assert a==2**length+sum(b*2**(length-1-j) for j,b in enumerate(bits))
            codes.append(a);count+=1
        assert codes==list(range(2**length,2**(length+1)))
    assert [bplus for bplus in range(1,20) if (bplus-1)*(bplus-2)==0]==[1,2]
    return count

class Evaluated(DAG):
    def __init__(self,values):super().__init__();self.values=values;self.actual=[];self.residuals=[]
    def val(self,x):return self.actual[x] if type(x) is int else self.values[x]
    def gate(self,op,a,b):
        aa,bb=self.val(a),self.val(b)
        out=super().gate(op,a,b)
        self.actual.append(aa*bb if op=='*' else aa+bb if op=='+' else aa-bb)
        return out
    def eq(self,a,b):
        super().eq(a,b);self.residuals.append(self.val(a)-self.val(b))

def polynomial_residual_checks():
    rng=random.Random(40174);count=0
    for L,R,W in itertools.product(range(4),range(4),[-1,0,1]):
        n=L+R;m=n+1;v=7
        z={p:rng.randrange(-5,6) for p in ['W','Wp','Q','InitialHead','InitialMemoryPlus','RawLeft','RawRight','HorizontalExtra','HalfRowsPower','HalfPeriodRepunit','PaddingPower']}
        z['W']=W
        z.update({'C:0':0,'C:1':1,'C:2':2})
        for c in ['Cx','Cu','C198','Cbase']:z['C:'+c]=rng.randrange(-5,6)
        for name,size in [('tile',v),('first',v),('anchor',584)]:
            for j in range(size):z[f'C:{name}:{j}']=rng.randrange(-3,4)
        for side,size in [('L',L),('R',R)]:
            for i in range(size):z[f'{side}{i}Plus']=rng.randrange(-3,4)
        dg=Evaluated(z);build(L,R,v,dag=dg)
        X,H,K,P=[z[a] for a in ['HorizontalExtra','HalfRowsPower','HalfPeriodRepunit','PaddingPower']]
        G=W**v;hx=X+1
        expected=[z['Wp']-1-z['C:Cx']*hx,H-1-(G-1)*K,z['Q']-H*H,H-P*G**m,z['InitialHead']-z['C:Cu']*H]
        bits=[]
        for side,size,raw in [('L',L,'RawLeft'),('R',R,'RawRight')]:
            bs=[z[f'{side}{i}Plus']-1 for i in range(size)];bits.append(bs)
            expected += [b*(b-1) for b in bs]
            expected.append(z[raw]-(2**size+sum(b*2**(size-1-j) for j,b in enumerate(bs))))
        tape=list(reversed(bits[0]))+[0]+bits[1]
        T=sum(b*G**(m-1-i) for i,b in enumerate(tape))
        A=sum(z[f'C:tile:{j}']*W**j for j in range(v))
        B=sum(z[f'C:first:{j}']*W**j for j in range(v))
        J=sum(z[f'C:anchor:{j}']*W**j for j in range(584))
        BG=K*(H+1)*(hx*A+z['Wp']*B)
        E=W**24000*T+G**R
        ZZ=W**23945+W**263945*(W**264000+1)*E
        DD=W**575450*G**n*J-z['C:C198']*(W+1)*ZZ
        expected.append(z['InitialMemoryPlus']-(BG+z['C:Cbase']*P*DD+1))
        assert dg.residuals==expected,(L,R,W,dg.residuals,expected)
        z.update(DilationA=G**n,DilationB=G**R,DilationT=T)
        wrapper=Evaluated(z);build_uniform_wrapper(v,dag=wrapper)
        assert wrapper.residuals==expected[:5]+expected[-1:]
        count+=1
    return count

def main():
    data=(ROOT/'data/anchor_patch.json').read_bytes()
    assert hashlib.sha256(data).hexdigest()==PIN
    anchor=json.loads(data)['patch']
    dense,boundaries=periodic_checks()
    patch=patch_checks(anchor)
    structural=0
    for L,R,v in itertools.product(range(8),range(8),[2,7,11]):
        got=build(L,R,v);want=closed_cost(L,R,v)
        assert all(got[k]==val for k,val in want.items()),(got,want)
        structural+=1
    stream=build(0,0)
    assert all(stream[k]==val for k,val in closed_cost(0,0).items())
    wrapper_stream=build_uniform_wrapper()
    assert all(wrapper_stream[k]==val for k,val in uniform_wrapper_cost().items())
    strict=strict_cost()
    # Independent dense Horner-cost formula and arithmetic constants.
    assert strict['total']==2*V*(U-1)+2*584*220+4+sum(chain(e) for e in [U,U-219,198])
    result={'status':'PASS','periodic_dense_boards':dense,'width_boundary_checks':boundaries,'patch_identity':patch,'raw_word_cases':raw_checks(),'dag_structural_cases':structural,'signed_residual_comparisons':polynomial_residual_checks(),'full_literal_empty_dag':stream,'full_conditional_uniform_wrapper':wrapper_stream,'strict_constant_prefix':strict,'scope':'Own-code arithmetic checks only; no upstream execution, giant dense board, all-length dilation, parent Pell witnesses, or literal constant-prefix expansion'}
    expected=json.loads((ROOT/'verification.json').read_text())
    assert result==expected, 'Stored scientific receipt does not match fresh result'
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
