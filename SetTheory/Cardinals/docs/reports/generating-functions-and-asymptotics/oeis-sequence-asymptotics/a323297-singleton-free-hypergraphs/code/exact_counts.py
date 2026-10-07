#!/usr/bin/env python3
"""Bounded exact verification for the hypergraphs in OEIS A323297/A323296.

No asymptotic theorem or effective onset is certified by these finite checks.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
from itertools import combinations
from math import comb, factorial
from common import emit, integer, new_file_path, require

MAX_N=640
MARKED_MAX=32
DIRECT_MAX=8
A_PREFIX=(1,1,1,2,16,76,271,1212,10158,78290,503231,3495966,33016534,
327625520,3000119669,28185006956,308636238516,3631959615948,42031903439809,
493129893459310,6264992355842706,84639308481270656,1159506969481515271,16131054826385628592)
B_PREFIX=(1,0,0,1,11,10,25,406,4823,15436,72915,895180,11320441,71777498,
519354927,6155284240,82292879425,788821735656,7772567489083,98329764933354,
1400924444610675,17424772471470490,216091776292721021,3035845122991962688,46700545575567202903)


def _flags(isolates, tetrahedra):
    require(type(isolates) is bool, 'isolates must be a boolean')
    require(type(tetrahedra) is bool, 'tetrahedra must be a boolean')


def component_types(m, isolates=True, tetrahedra=True):
    """(multiplicity, edges, defect, isolate, T3, T4) for fixed labelled support."""
    integer(m,1,MAX_N,'component size'); _flags(isolates,tetrahedra)
    if m==1:return ((1,0,1,1,0,0),) if isolates else ()
    if m==2:return ()
    if m==3:return ((1,1,0,0,0,0),)
    if m==4:return ((6,2,0,0,0,0),(4,3,1,0,1,0),(1,4,2,0,0,1)) if tetrahedra else ((6,2,0,0,0,0),)
    return ((comb(m,2),m-2,0,0,0,0),)


def assembly_counts(n,isolates=True,tetrahedra=True):
    """Root the component containing the smallest label; exact integers."""
    integer(n,0,MAX_N,'n');_flags(isolates,tetrahedra)
    c=[0]+[sum(t[0] for t in component_types(m,isolates,tetrahedra)) for m in range(1,n+1)]
    a=[1]
    for size in range(1,n+1):
        value=0; choose=1
        for m in range(1,size+1):
            value+=choose*c[m]*a[size-m]
            choose=choose*(size-m)//m
        a.append(value)
    return tuple(a)


def exponential_sum_counts(n,isolates=True,tetrahedra=True):
    """Independent finite factorial sum and signed-polynomial convolution.

    exp(i*z+z^2*exp(z)/2) has nth EGF coefficient
    sum_k binom(n,2k)*(2k-1)!!*(k+i)^(n-2k).
    Multiply by exp(-z^2/2-z^3/3+5t*z^4/24).
    """
    integer(n,0,MAX_N,'n');_flags(isolates,tetrahedra)
    main=[]
    for size in range(n+1):
        value=0;matchings=1
        for k in range(size//2+1):
            if k:matchings*=2*k-1
            value+=comb(size,2*k)*matchings*(k+int(isolates))**(size-2*k)
        main.append(value)
    poly=[1]
    for size in range(1,n+1):
        poly.append(sum(comb(size-1,m-1)*c*poly[size-m]
                        for m,c in ((2,-1),(3,-2),(4,5*int(tetrahedra))) if size>=m))
    result=tuple(sum(comb(size,j)*poly[j]*main[size-j] for j in range(size+1)) for size in range(n+1))
    require(all(x>=0 for x in result),'finite exponential-sum positivity failure')
    return result


def marked_count(n,u=1,v=1,s=1,t3=1,t4=1,isolates=True):
    """Fully marked exact count: u^K v^E s^S t3^T3 t4^T4."""
    integer(n,0,MARKED_MAX,'n');_flags(isolates,True)
    for label,value in (('K',u),('E',v),('S',s),('T3',t3),('T4',t4)):integer(value,0,3,label+' marker')
    c=[0]+[sum(c*u*v**e*s**si*t3**a*t4**b for c,e,d,si,a,b in component_types(m,isolates)) for m in range(1,n+1)]
    a=[1]
    for size in range(1,n+1):a.append(sum(comb(size-1,m-1)*c[m]*a[size-m] for m in range(1,size+1)))
    return a[-1]


def marked_totals(n,isolates=True):
    """Exact raw numerators for count,K,K^2,D,D^2,KD, where D=E+2K-n."""
    integer(n,0,MAX_N,'n');_flags(isolates,True)
    rows=[(1,0,0,0,0,0)]
    types=[()]+[component_types(m,isolates) for m in range(1,n+1)]
    for size in range(1,n+1):
        out=[0]*6;choose=1
        for m in range(1,size+1):
            a,k,kk,d,dd,kd=rows[size-m]
            for count,edges,defect,s,t3,t4 in types[m]:
                w=choose*count
                vals=(a,k+a,kk+2*k+a,d+defect*a,dd+2*defect*d+defect**2*a,kd+d+defect*k+defect*a)
                for j,val in enumerate(vals):out[j]+=w*val
            choose=choose*(size-m)//m
        rows.append(tuple(out))
    return tuple(rows)


def shifted_moments(n,isolates=True):
    """Independent EGF products and finite shifts for the same raw numerators."""
    integer(n,0,MAX_N,'n');_flags(isolates,True)
    a=assembly_counts(n,isolates)
    c=[0]+[sum(t[0] for t in component_types(m,isolates)) for m in range(1,n+1)]
    k=[sum(comb(i,m)*c[m]*a[i-m] for m in range(1,i+1)) for i in range(n+1)]
    kk=[k[i]+sum(comb(i,m)*c[m]*k[i-m] for m in range(1,i+1)) for i in range(n+1)]
    def shift(values,i,j):return 0 if i<j else factorial(i)//factorial(i-j)*values[i-j]
    out=[]
    for i in range(n+1):
        d=int(isolates)*shift(a,i,1)+Fraction(shift(a,i,4),4)
        dd=(int(isolates)*(shift(a,i,1)+shift(a,i,2)+Fraction(shift(a,i,5),2))
            +Fraction(shift(a,i,4),3)+Fraction(shift(a,i,8),16))
        kd=d+int(isolates)*shift(k,i,1)+Fraction(shift(k,i,4),4)
        values=(a[i],k[i],kk[i],d,dd,kd)
        require(all(Fraction(v).denominator==1 for v in values),'marked shift integrality failure')
        out.append(tuple(int(v) for v in values))
    return tuple(out)


def exceptional_factorial_totals(n,isolates=True):
    """Mixed falling-factorial numerators of (S,T3,T4), total order at most three."""
    integer(n,0,MARKED_MAX,'n');_flags(isolates,True)
    keys=tuple((a,b,c) for a in range(4) for b in range(4-a) for c in range(4-a-b))
    rows=[{key:int(key==(0,0,0)) for key in keys}]
    for size in range(1,n+1):
        row={key:0 for key in keys}
        for m in range(1,size+1):
            for count,e,d,si,t3,t4 in component_types(m,isolates):
                indicators=(si,t3,t4);weight=comb(size-1,m-1)*count
                for key in keys:
                    value=rows[size-m][key]
                    for i in range(3):
                        if indicators[i] and key[i]:
                            lower=list(key);lower[i]-=1
                            value+=key[i]*rows[size-m][tuple(lower)]
                    row[key]+=weight*value
        rows.append(row)
    return tuple(rows)


def direct_distribution(n):
    """Enumerate every admissible actual edge set; key=(K,E,S,T3,T4)."""
    integer(n,0,DIRECT_MAX,'n')
    edges=[sum(1<<v for v in triple) for triple in combinations(range(n),3)]
    allowed=[sum(1<<j for j in range(i+1,len(edges)) if (e&edges[j]).bit_count()!=1) for i,e in enumerate(edges)]
    dist=defaultdict(int)
    def visit(options,chosen):
        parents=list(range(n))
        def root(v):
            while parents[v]!=v:v=parents[v]
            return v
        for i in chosen:
            vertices=[v for v in range(n) if edges[i]>>v&1]
            for v in vertices[1:]:parents[root(v)]=root(vertices[0])
        comps={}
        for v in range(n):comps.setdefault(root(v),[0,0])[0]+=1
        for i in chosen:comps[root((edges[i]&-edges[i]).bit_length()-1)][1]+=1
        k=len(comps);e=len(chosen)
        s=sum(m==1 for m,f in comps.values());a=sum(m==4 and f==3 for m,f in comps.values());b=sum(m==4 and f==4 for m,f in comps.values())
        require(e+2*k-n==s+a+2*b,'direct edge-defect identity failure')
        dist[(k,e,s,a,b)]+=1
        while options:
            bit=options&-options;options-=bit;i=bit.bit_length()-1
            visit(options&allowed[i],chosen+(i,))
    visit((1<<len(edges))-1,())
    return dict(sorted(dist.items()))


def integer_digest(values):
    require(isinstance(values,(tuple,list)) and len(values)<=6*(MAX_N+1),'invalid hash sequence')
    require(all(type(x) is int and x.bit_length()<=100000 for x in values),'invalid hash integer')
    h=hashlib.sha256()
    for value in values:
        raw=abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'big')
        h.update(bytes([int(value<0)]));h.update(len(raw).to_bytes(4,'big'));h.update(raw)
    return h.hexdigest()


def verify(n=MAX_N):
    integer(n,24,MAX_N,'verification n')
    checks=[];counts={};moments={}
    for isolates,name,prefix in ((True,'A323297',A_PREFIX),(False,'A323296',B_PREFIX)):
        a=assembly_counts(n,isolates);b=exponential_sum_counts(n,isolates)
        require(a==b,'component recurrence versus exponential-sum convolution disagree: '+name)
        require(a[:len(prefix)]==prefix,name+' published prefix mismatch')
        counts[name]=a
        rows=marked_totals(n,isolates)
        require(rows==shifted_moments(n,isolates),'independent marked identities disagree')
        require(tuple(row[0] for row in rows)==a,'marked count mismatch')
        moments[name]=integer_digest([value for row in rows for value in row])
        checks.append(name+': component recurrence versus exponential-sum convolution and two moment routes through n='+str(n))
    for isolates in (True,False):
        require(assembly_counts(n,isolates,False)==exponential_sum_counts(n,isolates,False),'deleted tetrahedra independent-count mismatch')
    a=counts['A323297'];b=counts['A323296']
    for i in range(n+1):require(a[i]==sum(comb(i,j)*b[j] for j in range(i+1)),'binomial isolate transform failure')
    checks.append('isolate binomial transform and deletion specializations through n='+str(n))
    exceptional_hashes={}
    for isolates,name in ((True,'A323297'),(False,'A323296')):
        raw=exceptional_factorial_totals(MARKED_MAX,isolates)
        base=assembly_counts(MARKED_MAX,isolates)
        for size,row in enumerate(raw):
            for (aa,bb,cc),value in row.items():
                loss=aa+4*bb+4*cc
                expected=Fraction(0) if size<loss else Fraction(int(isolates)**aa*factorial(size)*base[size-loss],factorial(size-loss)*6**bb*24**cc)
                require(value==expected,'exceptional factorial shift identity mismatch')
            require(marked_count(size,s=0,isolates=isolates)==assembly_counts(size,False)[-1],'zero isolate marker mismatch')
            require(marked_count(size,t3=0,t4=0,isolates=isolates)==assembly_counts(size,isolates,False)[-1],'zero tetrahedra markers mismatch')
        exceptional_hashes[name]=integer_digest([value for row in raw for value in row.values()])
    checks.append('all mixed exceptional factorial moments through total order three and zero markers through n=32')
    direct=[]
    for size in range(DIRECT_MAX+1):
        dist=direct_distribution(size)
        require(sum(dist.values())==a[size],'direct A count mismatch')
        connected=sum(c for (k,e,s,x,y),c in dist.items() if k==1)
        expected_connected=sum(t[0] for t in component_types(size)) if size else 0
        require(connected==expected_connected,'direct connected multiplicity mismatch')
        require(sum(c for (k,e,s,x,y),c in dist.items() if s==0)==b[size],'direct B count mismatch')
        for markers in ((1,1,1,1,1),(2,3,1,2,3),(3,1,2,0,2),(1,2,0,3,0)):
            u,v,ss,t3,t4=markers
            expected=sum(c*u**k*v**e*ss**s*t3**x*t4**y for (k,e,s,x,y),c in dist.items())
            require(expected==marked_count(size,*markers),'direct full marking mismatch')
        for isolates in (True,False):
            values=[0]*6
            for (k,e,s,x,y),c in dist.items():
                if not isolates and s:continue
                d=s+x+2*y
                for j,v in enumerate((1,k,k*k,d,d*d,k*d)):values[j]+=c*v
            require(tuple(values)==marked_totals(size,isolates)[size],'direct moments mismatch')
        direct.append({'n':size,'total':a[size],'no_isolates':b[size],'joint_statistic_states':len(dist),'connected':connected})
    checks.append('actual-edge-set enumeration, connected multiplicities, defect identity, full marking, and moments through n=8')
    return {'status':'PASS','max_n':n,'checks':checks,'published_prefix_lengths':{'A323297':len(A_PREFIX),'A323296':len(B_PREFIX)},
            'count_sha256':{name:integer_digest(values) for name,values in counts.items()},
            'last_count_bit_lengths':{name:values[-1].bit_length() for name,values in counts.items()},
            'raw_moment_sha256':moments,'exceptional_factorial_sha256':exceptional_hashes,'direct_enumeration':direct,
            'integer_decimal_digit_cap':sys.get_int_max_str_digits(),
            'scope':'Exact finite integer/rational checks only; no asymptotic remainder or onset certification.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--n',type=int,default=MAX_N);parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(verify(args.n),args.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
