#!/usr/bin/env python3
"""Independent data-only manuscript checks. No packet code is imported/executed."""
import collections, functools, hashlib, json, pathlib, struct

OUT=pathlib.Path(__file__).resolve().parent
SCI=pathlib.Path('/workspace/shared/ant-fusion-next-20261004')
REL=pathlib.Path('/workspace/shared/ant-fusion-report48-release-20261004')
AUD=pathlib.Path('/workspace/shared/ant-fusion-independent-audit-20261004')
S=576000; R=601547591; L=240619037200; U=2*L
KINDS=('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def chain(n): return max(0,n.bit_length()+n.bit_count()-2)
def geo_count(n):
    return 2*(n.bit_length()-1)+n.bit_count()-1, n.bit_length()+n.bit_count()-2
result={}
paths=[p for root in (SCI,AUD) for p in root.rglob('*') if p.is_file()]
paths += [REL/n for n in ('Research_Report48.tex','block_groups.tex','release_evidence.tex','Research_Report48.pdf')]
before={str(p):[sha(p),p.stat().st_size,p.stat().st_mode,p.stat().st_mtime_ns] for p in paths}
(OUT/'input-snapshot.json').write_text(json.dumps(before,indent=2)+'\n')

# Authenticate all supplied local finite inputs and the science-package copy.
pins=read(SCI/'INPUT_PINS.json')
for name,row in pins.items(): assert sha(SCI/name)==row['sha256'],name
for p in SCI.rglob('*'):
    if p.is_file(): assert p.read_bytes()==(REL/'science'/p.relative_to(SCI)).read_bytes(),p
result['authenticated_input_files']=len(pins)
result['science_release_bytes_match']=True

# Decode all masks as finite fixed data, independently of the candidate loader.
base=SCI/'data/profiles'; profiles={}; manifest=read(base/'MANIFEST.json')
for name in ('H','B','F'):
    row=manifest['profiles'][name]
    assert sha(base/row['column_ids_file'])==row['column_ids_sha256']
    assert sha(base/row['dictionary_file'])==row['dictionary_sha256']
    dic=read(base/row['dictionary_file']); assert dic['height']==400 and dic['y0']==50
    masks=[int(x,16) for x in dic['mask_hex_by_id']]
    profiles[name]=[masks[i] for i in struct.unpack('<576000H',(base/row['column_ids_file']).read_bytes())]
profiles['Hlow']=[x%2**25 for x in profiles['H']]
profiles['Hhigh']=[x//2**25 for x in profiles['H']]
profiles['first']=[(x//2**25)%2 for x in profiles['H']]
q={}
for name in KINDS:
    row=manifest['corrections'][name]; assert sha(base/row['file'])==row['sha256']
    data=read(base/row['file']); assert data['width']==1200 and data['height']==400
    masks=[tuple(int(x,16) for x in pair) for pair in data['signed_masks_by_id']]
    assert all(0<=a<2**400 and 0<=b<2**400 and a&b==0 for a,b in masks)
    q[name]=[masks[i] for i in data['profile_id_by_dx']]; assert len(q[name])==1200

# Exhaust all exponent pairs; each applies independently to each of four kinds.
count=0
for phase in (0,S//2):
    for b,band in enumerate((range(51),range(51,651),range(651,1200))):
        assert len({(480-b-s-phase//600)%960 for s in range(957)})==957
        for s in range(957):
            k=(480-b-s-phase//600)%960
            for d in band:
                ell=50+600*b-d
                assert 0<=ell<600
                assert (288650-phase-600*(s+1)-d)%S==600*k+ell
                count+=1
result['exponent_identities']=count
result['formal_kind_term_identities']=4*count
assert count==2296800

def groups(a,phase):
    out=collections.defaultdict(list)
    for k in range(960): out[tuple(a[(288650-phase-600*k-r)%S] for r in range(600))].append(k)
    assert sorted(k for seq in out.values() for k in seq)==list(range(960))
    return out
def runs(seq):
    out=[]
    for k in seq:
        if out and out[-1][0]+out[-1][1]==k: out[-1][1]+=1
        else: out.append([k,1])
    return out
receipt=read(SCI/'fused-receipt.json')
allgroups={}; entries=0; block_counts={}
for name,a in profiles.items():
    for phase in (0,S//2):
        g=groups(a,phase); allgroups[name,phase]=g; entries+=600*960
        rec=receipt['block_array_identities'][name][str(phase)]
        assert rec['groups']==len(g)
        for (block,seq),r in zip(g.items(),rec['blocks']):
            assert r['positions']==seq and r['runs']==runs(seq)
            assert r['mask_tuple_sha256']==hashlib.sha256(json.dumps(block,separators=(',',':')).encode()).hexdigest()
    for block,seq in allgroups[name,0].items():
        assert sorted((k-480)%960 for k in seq)==allgroups[name,S//2][block]
    block_counts[name]=len(allgroups[name,0])
assert block_counts==dict(H=5,B=4,F=6,Hlow=3,Hhigh=5,first=4)
result['exact_profile_entries']=entries
result['block_counts']=block_counts

# Appendix groups must be the complete exact first-occurrence order.
appendix=[]
for line in (REL/'block_groups.tex').read_text().splitlines():
    if ' & ' not in line or line.startswith('\\toprule'): continue
    a,ix,pos=line.rstrip('\\').split(' & ')
    name={'$H$':'H','$B$':'B','$F$':'F','$H_{\\rm low}$':'Hlow','$H_{\\rm high}$':'Hhigh','first':'first'}[a]
    seq=[]
    for entry in pos.split(', '):
        ab=list(map(int,entry.split(':')))
        seq.extend(range(ab[0],ab[-1]+1))
    assert seq==list(allgroups[name,0].values())[int(ix)-1]
    appendix.append((name,int(ix)))
assert len(appendix)==27
result['appendix_groups_verified']=len(appendix)

# Paid profile identities as source-wire keys; zero aliases are common to widths.
zero=('zero',)
def key(w,p,m=0): return (w,p,m) if p or m else zero
prepared=set()
for name,w in [('H',400),('B',400),('F',400),('Hlow',25),('Hhigh',375)]:
    prepared.update(key(w,v) for v in profiles[name])
for pairs in q.values(): prepared.update(key(400,*pair) for pair in pairs)
prepared.discard(zero)
inventory=collections.Counter(k[0] for k in prepared)
assert inventory=={400:736,25:21,375:81}
req=[('H',S//2),('B',0),('B',S//2),('F',0),('F',S//2),('Hlow',0),('Hhigh',0),('first',0)]
blocks=set(); weights={}; groups_total=0; required=set()
for name,phase in req:
    for block,seq in allgroups[name,phase].items():
        w={'Hlow':25,'Hhigh':375,'first':1}.get(name,400)
        wires=tuple(('one',) if v else zero for v in block) if name=='first' else tuple(key(w,v) for v in block)
        if name!='first': required.update(x for x in wires if x!=zero)
        blocks.add(wires); weights.setdefault(tuple(seq),runs(seq)); groups_total+=1
for pairs in q.values(): required.update(key(400,*pair) for pair in pairs if any(pair))
assert required<=prepared and len(prepared)==838
assert len(blocks)==26 and len(weights)==18 and groups_total==37
result['paid_profile_inventory']={str(k):v for k,v in inventory.items()}
result['all_profile_requests_prepaid']=True

# Exact geometric polynomials represented coefficientwise in Z[Y].
def add(a,b):
    out=collections.Counter(a); out.update(b); return dict(out)
def mul(a,b):
    out=collections.Counter()
    for i,x in a.items():
        for j,y in b.items(): out[i+j]+=x*y
    return dict(out)
def geometric(n):
    p={1:1}; g={0:1}; m=a=0
    for bit in bin(n)[3:]:
        oldp=p; p=mul(p,p); g=add(g,mul(oldp,g));m+=2;a+=1
        if bit=='1': g=add(g,p);p=mul(p,{1:1});m+=1;a+=1
    assert p=={n:1} and g==dict.fromkeys(range(n),1)
    assert (m,a)==geo_count(n)
    return g,m,a
powers={0,1}; lengths={1}; run_products=run_additions=0
for seq,rr in weights.items():
    terms=[]
    for start,n in rr:
        powers.add(start);lengths.add(n)
        geom,_,_=geometric(n)
        term=mul({start:1},geom)
        terms.append(term)
        run_products+=int(start!=0 and n!=1)
    weight={}
    for term in terms: weight=add(weight,term)
    assert weight==dict.fromkeys(seq,1)
    run_additions+=len(rr)-1
pm=sum(chain(n) for n in powers if n not in (0,1))
gm=sum(geo_count(n)[0] for n in lengths);ga=sum(geo_count(n)[1] for n in lengths)
assert (pm,gm,ga,run_products,run_additions)==(119,168,104,13,7)
block_M=len(blocks)*599+groups_total+pm+gm+run_products
block_A=len(blocks)*599+groups_total-len(req)+ga+run_additions
assert (block_M,block_A)==(15911,15714)
result['weight_ledger']=dict(blocks=len(blocks),groups=groups_total,weights=len(weights),power_M=pm,geometric_M=gm,geometric_A=ga,run_M=run_products,run_A=run_additions,total_M=block_M,total_A=block_A,powers=sorted(powers),geometric_lengths=sorted(lengths))

# Independently count algebraic run lowering, using only fixed instruction JSON.
# No tape, ant, colored-map generator, saved prefix schedule, or packet code runs.
program=read(SCI/'data/physical_program.json')
interchange=(('DUP',0),('DUP',2),('DUP',1),('DUP',3),('NAND',2),('DUP',2),('NAND',1),('NAND',2),('NAND',1),('DUP',1),('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0),('DUP',1),('DUP',3),('NAND',2),('DUP',2),('NAND',1),('NAND',2),('NAND',1))
def word(op,distance):
    out=collections.Counter({('single',1):1})
    n=distance-(1 if op=='DUP' else 2)
    assert n>=0
    if n:out['directional',n]+=1
    return out
@functools.lru_cache(None)
def swap(distance):
    out=collections.Counter();delta=0
    for op,j in interchange:
        out.update(word(op,distance+delta-j));delta+=1 if op=='DUP' else -1
    assert delta==0 and sum(n*v for (_,n),v in out.items())==24*distance+14
    return out
@functools.lru_cache(None)
def copy(distance):
    out=word('DUP',distance)
    for offset in range(distance-1):out.update(swap(distance-offset))
    return out
run_counts=collections.Counter()
for node in program['nodes']:
    typ=node['type']
    if typ=='RANGE':
        n=len(range(node['start'],node['stop'],node['step']))
        if n: run_counts['directional',n]+=1
    elif typ=='ROW':run_counts['single' if node['op'] in ('DUP','NAND') else 'directional',1]+=1
    elif typ=='COPY':run_counts.update(copy(node['m']-node['i']))
    elif typ=='GATE':
        run_counts.update(copy(node['m']-node['u']));run_counts.update(copy(node['m']+1-node['v']));run_counts['single',1]+=1
    else:raise AssertionError(typ)
rows=sum(n*v for (_,n),v in run_counts.items()); assert rows==R==program['program_rows']
nr=sum(run_counts.values()); nd=sum(v for (kind,_),v in run_counts.items() if kind=='directional');ns=nr-nd
K=program['active_columns']-1; assert K==957
occM=chain(400)+sum(chain(n) for n in {n for _,n in run_counts} if n>1)+nr+4*K
occA=1+2*nd+ns+4*K+2*K
assert (occM,occA)==(5469985,8186999)
result['independent_occurrence_ledger']=dict(rows=rows,runs=nr,directional_runs=nd,singleton_runs=ns,M=occM,A=occA)

small=sum(v*(w-1) for w,v in inventory.items())
geomM,geomA=geo_count(R)
shiftM=geomM+sum(chain(n) for n in [375,L-425,L-400,L-25,U-25])
named=[chain(n) for n in [U,U-219,198,481225262775]]
assert named==[47,50,10,55]
prefix=dict(occurrence_constants=(occM,occA),small_profiles_and_basic_literals=(small,small+2),geometric_sum_and_fixed_shifts=(shiftM,geomA),anchor_rows=(584*220,584*220),remaining_named_constants=(sum(named)+1,5))
for name,(m,a) in prefix.items(): assert receipt['prefix_stages'][name]==dict(M=m,A=a,total=m+a)
prefixM=sum(m for m,a in prefix.values());prefixA=sum(a for m,a in prefix.values())
assert (prefixM,prefixA)==(5923373,8639993)
spatialM=chain(600)+12*599+24*959+24+block_M+8
spatialA=12*599+24*959+22+block_A+8
assert (spatialM,spatialA)==(46159,45948)
assert 31388831-(prefixM+prefixA+spatialM+spatialA+3461)==16729897
result['complete_ledger']=dict(prefix_M=prefixM,prefix_A=prefixA,spatial_M=spatialM,spatial_A=spatialA,removed_gates=4*(S-1),two_input_total=prefixM+prefixA+spatialM+spatialA+3461,one_input_total=prefixM+prefixA+spatialM+spatialA+3471,free_coefficient_two=spatialM+spatialA+3461,free_coefficient_one=spatialM+spatialA+3471,saving=16729897)

after={str(p):[sha(p),p.stat().st_size,p.stat().st_mode,p.stat().st_mtime_ns] for p in paths}
assert after==before
result['preserved_files']=len(before)
result['status']='PASS_INDEPENDENT_MANUSCRIPT_DATA_AND_LEDGER_CHECKS'
result['checker_sha256']=sha(pathlib.Path(__file__))
(OUT/'manuscript-check-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
