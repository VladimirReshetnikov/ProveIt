#!/usr/bin/env python3
"""Fresh static integer algebra; declared tables only. No program interpreter."""
from pathlib import Path
from math import comb, factorial, prod
from itertools import product
import json
import gzip
import hashlib
import time

OUT = Path(__file__).resolve().parent / 'evidence'

class Poly:
    def __init__(self, n, terms=None):
        self.n = n
        self.terms = {tuple(e): int(c) for e,c in (terms or {}).items() if c}
        assert all(len(e) == n and all(x >= 0 for x in e) for e in self.terms)
    def coerce(self, x):
        if isinstance(x, Poly):
            assert x.n == self.n
            return x
        return Poly(self.n, {(0,)*self.n: x})
    def __add__(self, other):
        other = self.coerce(other)
        d = dict(self.terms)
        for e,c in other.terms.items():
            d[e] = d.get(e, 0) + c
            if not d[e]: del d[e]
        return Poly(self.n, d)
    __radd__ = __add__
    def __neg__(self):
        return Poly(self.n, {e:-c for e,c in self.terms.items()})
    def __sub__(self, other): return self + -self.coerce(other)
    def __rsub__(self, other): return self.coerce(other) - self
    def __mul__(self, other):
        other = self.coerce(other)
        d = {}
        if self is other:
            items = list(self.terms.items())
            for i,(a,x) in enumerate(items):
                for j in range(i, len(items)):
                    b,y = items[j]
                    e = tuple(a[k]+b[k] for k in range(self.n))
                    d[e] = d.get(e, 0) + x*y*(1 if i == j else 2)
        else:
            for a,x in self.terms.items():
                for b,y in other.terms.items():
                    e = tuple(a[k]+b[k] for k in range(self.n))
                    d[e] = d.get(e, 0) + x*y
        return Poly(self.n, d)
    __rmul__ = __mul__
    def __pow__(self, k):
        assert isinstance(k, int) and k >= 0
        ans = self.coerce(1)
        base = self
        while k:
            if k & 1: ans = ans * base
            k //= 2
            if k: base = base * base
        return ans
    def degree(self): return max((sum(e) for e in self.terms), default=-1)
    def norm(self): return sum(abs(c) for c in self.terms.values())
    def evaluate(self, point):
        assert len(point) == self.n
        return sum(c * prod(x**a for x,a in zip(point,e)) for e,c in self.terms.items())
    def lift(self, n, positions):
        assert len(positions) == self.n and len(set(positions)) == self.n
        d = {}
        for e,c in self.terms.items():
            new = [0]*n
            for i,p in enumerate(positions): new[p] = e[i]
            d[tuple(new)] = c
        return Poly(n, d)
    def wire(self): return [[list(e), str(c)] for e,c in sorted(self.terms.items())]

def variable(n, i):
    e = [0]*n; e[i] = 1
    return Poly(n, {tuple(e): 1})

def product_poly(items, n):
    ans = Poly(n, {(0,)*n:1})
    for f in items: ans = ans * f
    return ans

def sos(residuals):
    assert residuals
    return sum((p*p for p in residuals), Poly(residuals[0].n))

def basis(k, z):
    return [(-1)**(k-i)*comb(k-1,i-1)*product_poly((z-h for h in range(1,k+1) if h != i), z.n)
            for i in range(1,k+1)]

def compiler(k, accepted):
    A,B,r,s = [variable(4,i) for i in range(4)]
    if k == 1:
        return [A-r, B-s, Poly(4), Poly(4), Poly(4,{(0,)*4:int((1,1) not in accepted)})]
    u,v = A-r+1, B-s+1
    left,right = basis(k,u),basis(k,v)
    f = sum((left[i-1]*right[j-1] for i,j in product(range(1,k+1), repeat=2) if (i,j) not in accepted), Poly(4))
    return [product_poly((u-i for i in range(1,k+1)),4), product_poly((v-i for i in range(1,k+1)),4), (r-1)*(u-k), (s-1)*(v-k), f]

def direct(k, accepted, A,B,r,s):
    if k == 1: return (A-r, B-s, 0, 0, int((1,1) not in accepted))
    u,v = A-r+1,B-s+1
    def vals(x):
        return [(-1)**(k-i)*comb(k-1,i-1)*prod(x-h for h in range(1,k+1) if h!=i) for i in range(1,k+1)]
    left,right = vals(u), vals(v)
    f = sum(left[i-1]*right[j-1] for i,j in product(range(1,k+1), repeat=2) if (i,j) not in accepted)
    return (prod(u-i for i in range(1,k+1)),prod(v-i for i in range(1,k+1)),(r-1)*(u-k),(s-1)*(v-k),f)

def module():
    names = ['C','o','g','q_b','q_v','J','q_alpha','d_wb_plus','d_wC_plus','d_yC_plus','q_sigma_plus','q_tau_plus','q_r_plus']
    C,o,g,qb,qv,J,qa,wb,wC,yC,qs,qt,qr = [variable(13,i) for i in range(13)]
    wb,wC,yC,qs,qt,qr = [x-1 for x in (wb,wC,yC,qs,qt,qr)]
    w,y = 2+wb,C+yC
    beta,v,t,mp,z = 1+4*y*qb,y*y*qv,C+4*y*qt,2*o+J,2*o+J+5
    x = y*(z-8)+8*o+4*mp*qr
    u = 4*beta-z
    vv = qa*x+u*qs
    hs = [x*x-16-(z*z-16)*y*y, u*u-16*qa*qa-(z*z-16)*qa*qa*v*v,
          vv*vv-16*qa*qa-16*qa*qa*(beta*beta-1)*t*t,
          w-C-wC, z*z-16-16*((w+1)*(w+1)-1)*(w*g)*(w*g)]
    return names, hs

def fixture(k):
    # Explicit accepted exponent-zero family; no recurrence or machine stepping.
    return [1,1,3,4+577*k,34,61,4*k,1,2,1,4*k+1,1,1]

def one_compiler(k, accepted):
    A,B,w=[variable(3,i) for i in range(3)]
    if k==1: return (w-1)*(w-1) if accepted else Poly(3,{(0,0,0):1})
    pa=product_poly(((A-h)*(A-h) for h in range(1,k)),3)
    pb=product_poly(((B-h)*(B-h) for h in range(1,k)),3)
    factors=[]
    for i,j in sorted(accepted):
        fixed=[]; target=Poly(3,{(0,0,0):1})
        if i<k: fixed.append(A-i)
        else: target=target*pa
        if j<k: fixed.append(B-j)
        else: target=target*pb
        factors.append(sos(fixed+[w-target]))
    return product_poly(factors,3)

def cell_witness(k,A,B):
    return prod(prod((x-h)**2 for h in range(1,k)) for x in (A,B) if x>=k)

def closure_holds(k,accepted):
    return all((a,b) in accepted for i,j in accepted
               for a in (range(1,k+1) if i==k else [i])
               for b in (range(1,k+1) if j==k else [j]))

def flat_value(k,accepted,A,B):
    return prod((0 if i==k else (A-i)**2)+(0 if j==k else (B-j)**2) for i,j in accepted)

def snapshot_like(before):
    now=[]
    for old in before:
        p=Path(old['path']); st=p.stat()
        row={'path':str(p),'mode':st.st_mode,'size':st.st_size,'mtime_ns':st.st_mtime_ns,'is_dir':p.is_dir()}
        if p.is_file(): row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
        now.append(row)
    return now

def main():
    start=time.time(); receipt={'method':'fresh static algebra and explicitly declared acceptance tables; no native or physical interpreter', 'checks':{}}
    expansions=[]; node_checks=0
    for k in range(1,10):
        z=variable(1,0); bs=basis(k,z); c=factorial(k-1)
        assert sum(bs,Poly(1)).terms == Poly(1,{(0,):c}).terms
        for i,b in enumerate(bs,1):
            for j in range(1,k+1):
                assert b.evaluate([j]) == (c if i==j else 0); node_checks+=1
    receipt['checks']['basis_node_identities']=node_checks
    for k in range(1,8):
        cells=set(product(range(1,k+1),repeat=2))
        tables={'empty':set(),'full':cells,'origin':{(1,1)},'diagonal':{(i,i) for i in range(1,k+1)},'checkerboard':{(i,j) for i,j in cells if (i+j)%2==0},'corner':{(k,k)}}
        for label,accepted in tables.items():
            ds=compiler(k,accepted); p=sos(ds)
            expected=2 if k==1 else max(2*k,4,2*ds[4].degree())
            assert p.degree()==expected
            if k>=2:
                bk=factorial(k+1); lk=2**(k-1)*bk
                assert p.norm() <= lk**4+2*bk*bk+8*(k+1)**2
                assert len(p.terms) <= k*k*(2*k-1)**2+8*k+2
                assert all(e[0]+e[2] <= 2*k and e[1]+e[3] <= 2*k for e in p.terms)
                if label=='origin': assert p.degree()==4*k-4
                if label in ('empty','full'): assert p.degree()==2*k
            else: assert len(p.terms)==(6 if accepted else 7)
            for A,B in product([1,k,k+1,2*k+7],repeat=2):
                r,s=A-min(A,k)+1,B-min(B,k)+1
                vals=direct(k,accepted,A,B,r,s)
                assert [d.evaluate([A,B,r,s]) for d in ds]==list(vals)
                assert p.evaluate([A,B,r,s])==sum(v*v for v in vals)
                assert (p.evaluate([A,B,r,s])==0)==((min(A,k),min(B,k)) in accepted)
            rec={'K':k,'table':label,'accepted':sorted(map(list,accepted)),'residual_degrees':[d.degree() for d in ds], 'degree':p.degree(),'monomials':len(p.terms),'max_coefficient_bits':max(abs(c).bit_length() for c in p.terms.values()),'coefficient_norm':str(p.norm())}
            receipt.setdefault('native_expansions',[]).append(rec)
            if label in ('origin','empty','full') and k<=4:
                expansions.append({'meta':rec,'variables':['A','B','r','s'],'residuals':[d.wire() for d in ds],'polynomial':p.wire()})
    receipt['checks']['native_expansions']=len(receipt['native_expansions'])
    box_checks=0
    for k in [1,2]:
        cells=list(product(range(1,k+1),repeat=2))
        for mask in range(1<<len(cells)):
            accepted={cell for i,cell in enumerate(cells) if mask>>i&1}
            ds=compiler(k,accepted); p=sos(ds)
            for A,B in product(range(1,6),repeat=2):
                zeros=[]
                for r,s in product(range(1,7),repeat=2):
                    val=direct(k,accepted,A,B,r,s)
                    actual=sum(v*v for v in val)
                    assert actual==p.evaluate([A,B,r,s]); box_checks+=1
                    if actual==0: zeros.append((r,s))
                expected=[(A-min(A,k)+1,B-min(B,k)+1)] if (min(A,k),min(B,k)) in accepted else []
                assert zeros==expected
    receipt['checks']['positive_witness_box_assignments']=box_checks
    table_checks=0; k=3; cells=list(product(range(1,4),repeat=2))
    for mask in range(1<<9):
        accepted={cell for i,cell in enumerate(cells) if mask>>i&1}
        for A,B in product(range(1,7),repeat=2):
            r,s=A-min(A,k)+1,B-min(B,k)+1
            vals=direct(k,accepted,A,B,r,s)
            assert (sum(v*v for v in vals)==0)==((min(A,k),min(B,k)) in accepted); table_checks+=1
    receipt['checks']['all_K3_tables_canonical_assignments']=table_checks
    # A deliberate excluded-domain counterexample: r=0 wrongly picks the tail.
    assert sum(x*x for x in direct(3,{(3,1)},2,1,0,1))==0
    receipt['checks']['zero_slack_domain_challenge']=True
    one_records=[]; one_assignments=0
    for k in [1,2,3]:
        cells=list(product(range(1,k+1),repeat=2))
        if k<=2:
            tables=[{cell for i,cell in enumerate(cells) if mask>>i&1} for mask in range(1<<len(cells))]
        else:
            tables=[set(),set(cells),{(1,1)},{(k,k)},{(1,k),(k,1)},{(1,1),(1,k),(k,1)}]
        for accepted in tables:
            q=one_compiler(k,accepted)
            ni=sum(i<k and j<k for i,j in accepted)
            ne=sum((i==k)+(j==k)==1 for i,j in accepted)
            nc=int((k,k) in accepted)
            degree=(2 if accepted else 0) if k==1 else 2*ni+4*(k-1)*ne+8*(k-1)*nc
            assert q.degree()==degree
            if k>=2:
                pk=factorial(k)**2
                mi,me,mc=2*k*k+4,k*k+(1+pk)**2,(1+pk*pk)**2
                assert q.norm()<=mi**ni*me**ne*mc**nc
                assert len(q.terms)<=comb(degree+3,3)
                assert degree<=10*(k-1)**2+8*(k-1)
            for A,B in product(range(1,6),repeat=2):
                cw=cell_witness(k,A,B)
                for w in sorted({1,2,3,4,5,6,cw,cw+1}):
                    val=q.evaluate([A,B,w])
                    assert val>=0
                    assert (val==0)==((min(A,k),min(B,k)) in accepted and w==cw)
                    one_assignments+=1
            rec={'K':k,'accepted':sorted(map(list,accepted)),'degree':degree,'monomials':len(q.terms),'max_coefficient_bits':max(abs(c).bit_length() for c in q.terms.values())}
            one_records.append(rec)
    closure_checks=0; closure_counts={}
    for k in [1,2,3]:
        cells=list(product(range(1,k+1),repeat=2)); count=0
        for mask in range(1<<len(cells)):
            accepted={cell for i,cell in enumerate(cells) if mask>>i&1}
            closed=closure_holds(k,accepted); count+=int(closed)
            actual=all((flat_value(k,accepted,A,B)==0)==((min(A,k),min(B,k)) in accepted)
                       for A,B in product(range(1,k+3),repeat=2))
            assert actual==closed; closure_checks+=1
        closure_counts[str(k)]=count
    receipt['one_witness_expansions']=one_records
    receipt['checks']['one_witness_assignments']=one_assignments
    receipt['checks']['zero_witness_closure_tables']=closure_checks
    receipt['zero_witness_closure_counts']=closure_counts
    dimension_checks=0
    for dimension in range(1,7):
        for t in range(1,6):
            # Count by number of tail coordinates, not by program execution.
            explicit=2*t**dimension+sum(comb(dimension,j)*t**(dimension-j)*4*t*j for j in range(1,dimension+1))
            assert explicit==2*t**dimension+4*dimension*t*(t+1)**(dimension-1)
            dimension_checks+=1
    receipt['checks']['d_input_degree_ledgers']=dimension_checks
    names,hs=module(); hp=sos(hs)
    assert [h.degree() for h in hs]==[4,10,10,1,6] and hp.degree()==20
    target=[0]*13
    for name,power in [('J',4),('q_alpha',4),('d_yC_plus',8),('q_v',4)]: target[names.index(name)]=power
    assert hp.terms[tuple(target)]==1
    for shift in [1,2,7]:
        point=fixture(shift)
        assert all(x>0 for x in point) and all(h.evaluate(point)==0 for h in hs)
    receipt['module']={'positive_leaves_including_output':12,'residuals':5,'degree':hp.degree(),'monomials':len(hp.terms),'coefficient_one_certificate':target,'declared_positive_fixture_shifts':[1,2,7]}
    fullnames=['g1','g2','g3','A','B','r','s']+['left_'+s for s in names[1:]]+['right_'+s for s in names[1:]]
    assert len(fullnames)==31 and len(set(fullnames))==31
    gl=[variable(31,i) for i in range(31)]
    g1,g2,g3=gl[:3]; D=g1+g2+g3; pp=gl[7]; qq=gl[19]
    gaps=[(20*g1-D)*pp-2*D,(20*g3-D)*qq-2*D]
    lhs=[h.lift(31,[3]+list(range(7,19))) for h in hs]
    rhs=[h.lift(31,[4]+list(range(19,31))) for h in hs]
    fixed=sos(gaps)+hp.lift(31,[3]+list(range(7,19)))+hp.lift(31,[4]+list(range(19,31)))
    compositions=[]; fixture_checks=0
    for k in [1,2,3,6,7]:
        for accepted in [set(),{(1,1)}]:
            ds=compiler(k,accepted); cp=sos(ds)
            cds=[d.lift(31,[3,4,5,6]) for d in ds]
            full=fixed+cp.lift(31,[3,4,5,6])
            residuals=gaps+lhs+rhs+cds
            assert len(residuals)==17 and full.degree()==max(20,cp.degree())
            assert {i for e in full.terms for i,p in enumerate(e) if p}==set(range(31))
            for leftk,rightk in [(1,1),(1,7),(7,2)]:
                point=[3,14,3,1,1,1,1]+fixture(leftk)[1:]+fixture(rightk)[1:]
                vals=[d.evaluate(point) for d in residuals]
                assert full.evaluate(point)==sum(v*v for v in vals)
                assert (full.evaluate(point)==0)==((1,1) in accepted)
                fixture_checks+=1
            changed=[4,14,3,1,1,1,1]+fixture(1)[1:]+fixture(1)[1:]
            assert full.evaluate(changed)>0
            rec={'K':k,'table':'empty' if not accepted else 'origin','witnesses':28,'inputs':3,'variables':31,'residuals':17,'compiler_degree':cp.degree(),'degree':full.degree(),'monomials':len(full.terms)}
            compositions.append(rec)
            if k in [1,6] and accepted:
                expansions.append({'meta':rec,'variables':fullnames,'polynomial':full.wire()})
    receipt['compositions']=compositions
    receipt['checks']['complete_gap_assignments']=fixture_checks
    onevars=[variable(30,i) for i in range(30)]
    ga,gb,gc=onevars[:3]; dd=ga+gb+gc
    ogaps=[(20*ga-dd)*onevars[6]-2*dd,(20*gc-dd)*onevars[18]-2*dd]
    obase=sos(ogaps)+hp.lift(30,[3]+list(range(6,18)))+hp.lift(30,[4]+list(range(18,30)))
    onecomps=[]
    for k,accepted in [(1,set()),(1,{(1,1)}),(2,set(product(range(1,3),repeat=2))),(3,{(1,1)}),(3,{(3,3)})]:
        q=one_compiler(k,accepted); q2=q*q
        plain=obase+q.lift(30,[3,4,5]); squared=obase+q2.lift(30,[3,4,5])
        assert plain.degree()==max(20,q.degree()) and squared.degree()==max(20,2*q.degree())
        for shift in [1,7]:
            point=[3,14,3,1,1,1]+fixture(shift)[1:]+fixture(1)[1:]
            assert (plain.evaluate(point)==0)==((1,1) in accepted)
            assert (squared.evaluate(point)==0)==((1,1) in accepted)
        onecomps.append({'K':k,'accepted':sorted(map(list,accepted)),'witnesses':27,'external_inputs':3,'total_variables':30,'plain_presentation':'12 squares plus one product-of-sums-of-squares block','squared_residual_slots':13,'compiler_degree':q.degree(),'plain_degree':plain.degree(),'squared_degree':squared.degree()})
    receipt['one_witness_compositions']=onecomps
    before=json.loads((OUT/'source_before.json').read_text())
    after=snapshot_like(before)
    changes=[{'before':a,'after':b} for a,b in zip(before,after) if a!=b]
    # Report 68 is concurrently being released by a separate task. The first
    # run detected its README/mode updates; retain, do not conceal, that delta.
    assert all('/report68-gap-statistics-release-20261004' in x['before']['path'] for x in changes)
    (OUT/'concurrent_source_changes.json').write_text(json.dumps(changes,indent=2)+'\n')
    (OUT/'source_after.json').write_text(json.dumps(after,indent=2)+'\n')
    receipt['source_preservation']={'entries':len(after),'arithmetic_sources_and_reports66_67_unchanged':True,'concurrent_report68_changed_entries':len(changes),'changes_file':'concurrent_source_changes.json','access_times_excluded':True,'source_tree_writes_by_this_checker':False}
    sealed_before=json.loads((OUT/'report68_postseal_before.json').read_text())
    sealed_after=snapshot_like(sealed_before)
    assert sealed_before==sealed_after
    (OUT/'report68_postseal_after.json').write_text(json.dumps(sealed_after,indent=2)+'\n')
    receipt['source_preservation']['report68_postseal_entries_unchanged']=len(sealed_after)
    pins=json.loads((OUT.parent/'SOURCE_PINS.json').read_text())
    for pin in pins:
        data=(OUT.parent/pin['file']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==pin['sha256'] and len(data)==pin['bytes']
    receipt['dependency_pins_verified']=len(pins)
    with gzip.open(OUT/'expanded_polynomials.json.gz','wt',encoding='utf-8') as f:
        json.dump(expansions,f,separators=(',',':'))
    receipt['seconds']=round(time.time()-start,3)
    (OUT/'results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':receipt['checks'],'native_expansions':len(receipt['native_expansions']),'compositions':len(compositions),'source_entries_unchanged':len(after)-len(changes),'concurrent_report68_changed_entries':len(changes),'seconds':receipt['seconds']},indent=2))

if __name__=='__main__': main()
