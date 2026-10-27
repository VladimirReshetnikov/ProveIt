"""Independent exact-oracle audit of the new ratio-fused component.

Only newly authored local modules are imported. No archive code is executed.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,hashlib,statistics,random
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from cauchy_kernel import Parameters, Ring as BasicRing, recurrent_tables
from fused_cauchy import Prepared, MaskRing, baseline_tables, fused_tables
counts={}
def require(ok,message):
    if not ok:raise ArithmeticError(message)
def bump(name,n=1):counts[name]=counts.get(name,0)+n

# Exact arithmetic in Q[U]/(U^2+U+1), with no kernel helper imports.
def mul(x,y):
    a,b=x; c,d=y
    return a*c-b*d, a*d+b*c-b*d
def div(x,y):
    c,d=y; norm=c*c-c*d+d*d
    return mul(x,((c-d)/norm,-d/norm))
def scale(x,s):return x[0]*s,x[1]*s
def red(x,p):
    m=1<<p
    for c in x:require(c.denominator&1,'nonintegral oracle coefficient')
    return tuple(c.numerator*pow(c.denominator,-1,m)%m for c in x)
def v2(n):
    require(n!=0,'valuation oracle zero')
    a=0
    while n%2==0:n//=2;a+=1
    return a

def exact_tables(a,i,t,zeta):
    L=1<<a;R=1<<i;N=L//2
    slots=[x for x in range(L) if (x//R)%2==0]
    T=F(t+2*L*zeta[0]),F(2*L*zeta[1])
    pref=(F(1),F(0))
    for q in range(-L,L):
        if q:pref=mul(pref,scale((T[0]-q,T[1]),F(-1,q)))
    tables=[[],[]]
    for side in (0,1):
        for b,pivot in enumerate(slots):
            E=2*(b//R)-(b//R).bit_count()
            row=[]
            for x in slots:
                d=(x-pivot)*(1 if side==0 else -1)
                feature=div(T,(T[0]+d,T[1]))
                for previous in slots[:b]:
                    d=(x-previous)*(1 if side==0 else -1)
                    feature=div(scale(feature,d),(T[0]+d,T[1]))
                row.append(scale(mul(pref,feature),1<<E) if side==0 else scale(feature,F(1,1<<E)))
            tables[side].append(row)
    for j,x in enumerate(slots):
        for k,y in enumerate(slots):
            reconstructed=[F(0),F(0)]
            for b in range(N):
                term=mul(tables[0][b][j],tables[1][b][k])
                reconstructed=[reconstructed[h]+term[h] for h in (0,1)]
            require(tuple(reconstructed)==div(mul(pref,T),(T[0]+x-y,T[1])),'exact Cauchy reconstruction')
            bump('exact_cauchy_reconstructions')
    return tables

for a in range(1,5):
    L=1<<a;N=L//2
    for t in range(-L,L):
        if not t or v2(t)>=a:continue
        i=v2(t);R=1<<i
        for zeta in ((0,0),(0,1),(1,1),(-2,3),(3,-4)):
            exact=exact_tables(a,i,t,zeta)
            bump('all_grid_rational_configurations')
            for p in (1,3,9,17):
                params=Parameters(a,i,t,zeta,p)
                base,new,prior=baseline_tables(params),fused_tables(params),recurrent_tables(params)
                for side,key in enumerate(('target','source')):
                    expected=[[red(x,p) for x in row] for row in exact[side]]
                    require(base[key]==new[key]==prior[key]==expected,'fused exact feature mismatch')
                    bump('exact_feature_equalities',N*N)
                K=(2*N//R-1)*(2*R-1);g=1 if R==1 else 2
                b,n=base['counts'],new['counts']
                require(b['unit_inversions']==n['unit_inversions']==1,'one-inverse mismatch')
                require(b['common_preparation_multiplications']==n['common_preparation_multiplications'],'common setup mismatch')
                require(b['table_multiplications']==(5*N*N+N)//2,'baseline table count')
                require(n['table_multiplications']==N*N+N,'fused table count')
                require(n['ratio_cache_entries']==g*(K+1),'ratio cache count')
                require(n['preparation_multiplications']==b['preparation_multiplications']+g*(K+1)+1,'fused prep count')
                for result in (base,new):
                    c=result['counts'];require(c['total_multiplications']==c['preparation_multiplications']+c['table_multiplications'],'total count')
                if zeta!=(0,0):require(b['preparation_multiplications']==3*K+2*L+3,'nonzero-prefactor setup count')
                else:
                    require(all(x==(0,0) for row in new['target'] for x in row),'zero target prefactor')
                    bump('zero_prefactor_configurations')
                bump('modular_configurations');bump('operation_count_checks',8)

# Exact state valuations are independent of low-precision displayed zeros.
recovery=Parameters(3,0,1,(1,0),1)
q=exact_tables(3,0,1,(1,0));out=fused_tables(recovery)
require(red(q[1][1][2],1)==(0,0) and red(q[1][2][2],1)!=(0,0),'exact recovery fixture')
require(out['source'][1][2]==(0,0) and out['source'][2][2]!=(0,0),'fused recovery fixture')
bump('explicit_zero_then_nonzero_recovery_controls')
# Large signed shift coordinates must be split before modular reduction.
for zeta in ((1<<67, -(1<<61)+1),(-(1<<71)+3,1<<65)):
    exact=exact_tables(3,0,-7,zeta)
    for p in (1,2,5):
        params=Parameters(3,0,-7,zeta,p);base,new=baseline_tables(params),fused_tables(params)
        for side,key in enumerate(('target','source')):
            expected=[[red(x,p) for x in row] for row in exact[side]]
            require(base[key]==new[key]==expected,'large-coordinate exact check')
            bump('large_coordinate_feature_equalities',len(expected)**2)
        bump('large_coordinate_configurations')

# Independent enumeration of difference keys and actual consecutive gaps.
for a in range(1,7):
    for i in range(a):
        k=Prepared(Parameters(a,i,1<<i,(0,1),3))
        expected={x-y for x in k.slots for y in k.slots}
        require(set(k.differences)==expected and len(k.differences)==len(expected),'difference cache exactness')
        allowed={2} if i==0 else {1,(1<<i)+1}
        require({y-x for x,y in zip(k.slots,k.slots[1:])}<=allowed,'gap support')
        bump('difference_gap_cache_controls')

# Mask arithmetic must equal the independently retained modulo backend,
# including negative/unreduced coordinates and precision beyond machine words.
rng=random.Random(2026102702)
for precision in (1,2,5,17,65,257):
    basic,masked=BasicRing(precision),MaskRing(precision)
    units=[]
    for iteration in range(70):
        def coordinate():
            v=rng.getrandbits(precision+33)
            return -v if rng.randrange(2) else v
        x=(coordinate(),coordinate());y=(coordinate(),coordinate())
        require(masked.reduce(x)==basic.reduce(x),'mask reduction')
        require(masked.add(x,y)==basic.add(x,y),'mask addition')
        require(masked.mul(x,y)==basic.mul(x,y),'mask multiplication')
        bump('mask_basic_arithmetic_equalities',3)
        for power in (0,1,precision-1,precision,precision+1):
            require(masked.scale_two(x,power)==basic.scale_two(x,power),'mask scaling')
            bump('mask_basic_shift_equalities')
        if x[0]%2 or x[1]%2:
            units.append(x)
            require(masked.inverse(x)==basic.inverse(x),'mask inverse')
            require(masked.mul(x,masked.inverse(x))==(1,0),'mask inverse identity')
            # Keep counter workloads equal after identity verification.
            require(basic.mul(x,basic.inverse(x))==(1,0),'basic inverse identity')
            bump('mask_basic_unit_inverse_equalities')
        else:
            for ring in (basic,masked):
                try:ring.inverse(x)
                except ValueError:bump('mask_basic_nonunit_rejections')
                else:raise ArithmeticError('nonunit inverted')
    require(masked.batch_inverse(units)==basic.batch_inverse(units),'mask batch inverse')
    require(masked.batch_inverse([])==basic.batch_inverse([])==[],'mask empty batch')
    bump('mask_basic_batch_controls',2)
    for ring in (basic,masked):
        for x in ((0,0),(2,0),(0,-2),(-2,2)):
            try:ring.inverse(x)
            except ValueError:bump('mask_basic_nonunit_rejections')
            else:raise ArithmeticError('fixed nonunit inverted')
        try:ring.scale_two((-1,2),-1)
        except ArithmeticError:bump('negative_shift_rejections')
        else:raise ArithmeticError('negative shift accepted')
    require(basic.multiplications==masked.multiplications and basic.inversions==masked.inversions,'mask count consistency')
    bump('mask_basic_count_controls')

path=ROOT/'results/fused_cauchy_benchmark_mask_all.json'
data=json.loads(path.read_text());records=data['records']
# The final benchmark combines two disjoint measured fixture groups, not
# selected favorable repetitions. Verify raw bytes and the complete union.
raw_union=[];raw_hashes={}
require(len(data['provenance'])==2,'unexpected provenance group count')
for row in data['provenance']:
    require(Path(row['file']).name==row['file'],'unsafe provenance filename')
    rawpath=ROOT/'results'/row['file']
    digest=hashlib.sha256(rawpath.read_bytes()).hexdigest()
    require(digest==row['sha256'],'raw benchmark hash')
    raw=json.loads(rawpath.read_text())
    require(raw['status']=='PASS' and raw['repeats']==5,'raw benchmark status')
    raw_union.extend(raw['records']);raw_hashes[row['file']]=digest
    bump('benchmark_provenance_file_checks')
require(raw_union==records,'benchmark concatenation changed samples')
keys=[(r['a'],r['i'],r['N'],r['precision']) for r in records]
require(len(set(keys))==len(keys),'duplicate benchmark fixture')
expected={(a,i,1<<(a-1),4*(1<<(a-1))+16) for a in range(2,10) for i in {0,a//2,a-1}}
require(set(keys)==expected,'benchmark fixture coverage')
require('MaskRing' in data['backend'],'final benchmark backend mismatch')
bump('benchmark_provenance_union_checks')
for r in records:
    N=r['N'];R=1<<r['i'];L=2*N;K=(2*N//R-1)*(2*R-1);g=1 if R==1 else 2
    for method in ('baseline','fused'):
        for samples,median in ((r['wall_samples'][method],r[method+'_median_seconds']),(r['cpu_samples'][method],r[method+'_median_cpu_seconds'])):
            require(len(samples)==data['repeats']==5 and min(samples)>0,'benchmark samples')
            require(statistics.median(samples)==median,'benchmark median')
        c=r[method+'_counts']
        require(c['unit_inversions']==1 and c['common_preparation_multiplications']==3*K+2*L+3,'benchmark shared prep')
        expected=(5*N*N+N)//2 if method=='baseline' else N*N+N
        extra=0 if method=='baseline' else g*(K+1)+1
        require(c['table_multiplications']==expected and c['total_multiplications']==3*K+2*L+3+extra+expected,'benchmark counts')
    require(r['wall_speedup']==r['baseline_median_seconds']/r['fused_median_seconds'],'wall ratio')
    require(r['cpu_speedup']==r['baseline_median_cpu_seconds']/r['fused_median_cpu_seconds'],'CPU ratio')
    require(r['precision']==4*N+16,'growing precision')
    bump('benchmark_records')
hashes={name:hashlib.sha256((ROOT/'code'/name).read_bytes()).hexdigest() for name in ('fused_cauchy.py','verify_fused_cauchy.py','benchmark_fused_cauchy.py','cauchy_kernel.py')}
result={'status':'PASS','optimization':sys.flags.optimize,'counts':counts,'source_sha256':hashes,'benchmark_file':path.name,'benchmark_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'benchmark_raw_sha256':raw_hashes,'benchmark_summary':{'wall_range':[min(r['wall_speedup'] for r in records),max(r['wall_speedup'] for r in records)],'CPU_range':[min(r['cpu_speedup'] for r in records),max(r['cpu_speedup'] for r in records)],'wall_regressions':sum(r['wall_speedup']<1 for r in records),'largest_N':[{'N':r['N'],'i':r['i'],'wall_speedup':r['wall_speedup'],'cpu_speedup':r['cpu_speedup']} for r in records if r['N']==max(x['N'] for x in records)]},'scope':'Finite independent rational-oracle component audit; not end-to-end SAT, a universal speedup, or arbitrary-extension-degree certification. No incoming code executed.'}
dest=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'qa'/('fused_audit_checks_optimized.json' if sys.flags.optimize else 'fused_audit_checks_normal.json')
dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
