#!/usr/bin/env python3
"""Independent algebra/data audit. Never import or execute the frozen programs.

Inspected inputs are finite JSON maps and compressed node descriptions. The
counter below aggregates word-distance histograms; it does not produce or query
the physical instruction schedule. Synthetic polynomials have no ant semantics.
"""
import ast
import collections
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ASSETS = Path('/workspace/shared/report44-recovery-20261004/certificate/dependencies/recipe_assets')
CANDIDATE = Path('/workspace/shared/ant-coefficient-compression/occurrence_compiler.py')

def need(ok, detail):
    if not ok:
        raise ValueError(detail)

def load(path):
    return json.loads(path.read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def chain(n):
    return 0 if n < 2 else n.bit_length() + n.bit_count() - 2

def occurrence_counts():
    path = ASSETS / 'ca/physical_program.json'
    p = load(path)
    # Finite word-level mathematical interchange, inspected in frozen source.
    xor = [('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0)]
    interchange = [('DUP',0),('DUP',2)] + [(o,j+1) for o,j in xor] + [('DUP',1)] + xor + [(o,j+1) for o,j in xor]
    # Parse the candidate's literal declaration, never import it.
    tree = ast.parse(CANDIDATE.read_text())
    candidate_spec = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign) and any(isinstance(t,ast.Name) and t.id=='INTERCHANGE' for t in n.targets))
    need(list(candidate_spec)==interchange, 'Interchange differs from finite specification')
    copies = collections.Counter()
    lengths = set([1])
    directional = singleton = rows = 0
    boundaries = [0]
    direct_top = 0
    def copy_length(d):
        need(d>=1, 'Invalid COPY distance')
        return 12*d*d + 27*d - 38
    for n in p['nodes']:
        typ=n['type']
        if typ=='COPY':
            d=n['m']-n['i']; copies[d]+=1; amount=copy_length(d)
        elif typ=='GATE':
            a=n['m']-n['u']; b=n['m']+1-n['v']
            copies[a]+=1; copies[b]+=1; amount=copy_length(a)+copy_length(b)+1
            direct_top+=1
        elif typ=='RANGE':
            amount=len(range(n['start'],n['stop'],n['step']))
            need(n['op'] in ('MOVE_LEFT','MOVE_RIGHT'), 'Unexpected RANGE')
            if amount:
                lengths.add(amount); directional+=1
        elif typ=='ROW':
            need(n['op'] in ('DUP','NAND'), 'Unexpected ROW')
            amount=1;direct_top+=1
        else:
            raise ValueError(typ)
        rows+=amount;boundaries.append(rows)
    # A COPY at distance d consists of DUP(d), then interchanges at distances
    # d,d-1,...,2. Aggregate their multiplicities instead of enumerating rows.
    swaps=collections.Counter({d:sum(v for k,v in copies.items() if k>=d) for d in range(2,max(copies)+1)})
    words=collections.Counter({('DUP',d):v for d,v in copies.items()})
    for d,multiplicity in swaps.items():
        delta=0
        for op,j in interchange:
            words[op,d+delta-j]+=multiplicity
            delta+=1 if op=='DUP' else -1
        need(delta==0, 'Interchange width not conserved')
    singleton=direct_top
    for (op,d),multiplicity in words.items():
        need(d >= (1 if op=='DUP' else 2), 'Invalid finite word distance')
        singleton+=multiplicity
        travel=d-(1 if op=='DUP' else 2)
        if travel:
            directional+=multiplicity;lengths.add(travel)
    runs=singleton+directional
    K=p['active_columns']-1
    countM=chain(400)+runs+4*K+sum(chain(n) for n in lengths)
    countA=1+singleton+2*directional+6*K
    result=dict(runs=runs,directional_runs=directional,singleton_runs=singleton,
                words=sum(words.values()),interchanges=sum(swaps.values()),
                copies=sum(copies.values()),time_rows=rows,top_level_nodes=len(p['nodes']),
                cached_lengths=len(lengths)+1,
                boundary_sha256=hashlib.sha256(json.dumps(boundaries,separators=(',',':')).encode()).hexdigest(),
                source=dict(M=countM,A=countA,total=countM+countA),
                cached_power_cost=sum(chain(n) for n in lengths))
    receipt=load(CANDIDATE.with_name('occurrence-receipt.json'))
    for key in result:
        if key=='source':
            need(all(result[key][k]==receipt[key][k] for k in ('M','A','total')), (key,result[key],receipt[key]))
        elif key!='cached_power_cost':
            need(result[key]==receipt[key], (key,result[key],receipt[key]))
    need(rows==p['program_rows'], 'Total row count differs')
    result['program_sha256']=digest(path)
    result['candidate_sha256']=digest(CANDIDATE)
    result['saved_schedule_read']=False
    return result

def polynomial_events():
    # Compare exact coefficient dictionaries, not evaluations at sampled bases.
    def plus(p,q):
        r=collections.Counter(p)
        for e,c in q.items():r[e]+=c
        return {e:c for e,c in r.items() if c}
    def shift(p):return {e+1:c for e,c in p.items()}
    tested=0
    for K in range(1,13):
        for direction in (-1,1):
            for s in range(K):
                for length in range(1,(K-s if direction==1 else s+1)+1):
                    for n in range(4):
                        events=[{} for _ in range(K+2)]
                        events[s+1]={n:1}
                        end=s+direction*length
                        events[end+1]=plus(events[end+1],{n+length:-1})
                        actual=[None]*K;prev={}
                        for slot in (range(K) if direction==1 else range(K-1,-1,-1)):
                            prev=plus(shift(prev),events[slot+1]);actual[slot]=prev
                        expected=[{} for _ in range(K)]
                        for k in range(length):expected[s+direction*k]={n+k:1}
                        need(actual==expected,('Event identity',K,s,length,n,direction))
                        tested+=1
    return dict(exact_symbolic_interval_tests=tested,maximum_slots=12,
                general_proof='Linearity plus a single run: at displacement k, the start event contributes Z^(n+k); at k=L the stop event cancels this term and all its future shifts. Exterior stop events affect no owned slot.')

def motif_checks():
    file_names={'delay':'copy/delayed_copy.json','dup':'copy/pair_dup.json','left':'copy/pair_move_left.json','right':'copy/pair_move_right.json','not':'not/normalized_not.json','copy':'copy/normalized_copy.json','left_marker':'copy/marker_left_start.json','right_marker':'copy/marker_right_stop.json','nand_raw':'nand/nand_macro.json'}
    maps={};pins={}
    for name,rel in file_names.items():
        path=ASSETS/rel;data=load(path)['board'];m={}
        for x,y,c in data:
            need(c in (0,1),('Nonbinary color',name))
            need((x,y) not in m,('Duplicate source cell',name,x,y))
            m[x,y]=c
        maps[name]=m;pins[rel]=digest(path)
    def shifted(m,x=0,y=0):return {(a+x,b+y):v for (a,b),v in m.items()}
    def united(*parts):
        r={}
        for m in parts:
            for q,c in m.items():
                need(q not in r or r[q]==c,('Conflicting finite union',q))
                r[q]=c
        return r
    def black(m):return {q for q,c in m.items() if c==1}
    maps['nand']=united(maps['nand_raw'],shifted(maps['copy'],y=200),shifted(maps['copy'],x=600,y=200))
    base=united(maps['delay'],shifted(maps['delay'],x=600))
    corr={}
    for op in ('dup','left','right','nand'):
        positive=black(maps[op])-black(base);negative=black(base)-black(maps[op])
        all_delta=positive|negative
        need(all(50<=y<450 for x,y in all_delta),('Correction crosses owned slab',op))
        corr[op]=dict(positive=len(positive),negative=len(negative),bounds=[min(x for x,y in all_delta),max(x for x,y in all_delta),min(y for x,y in all_delta),max(y for x,y in all_delta)])
        # Independently verify every published signed correction mask, not only
        # its count or bounding box.
        public={'dup':'DUP','left':'MOVE_LEFT','right':'MOVE_RIGHT','nand':'NAND'}[op]
        qpath=Path('/workspace/shared/ant-motif-overlap/profiles')/f'Q_{public}.json'
        q=load(qpath);decoded=[(int(a,16),int(b,16)) for a,b in q['signed_masks_by_id']]
        actual_plus=set();actual_minus=set()
        for x,i in enumerate(q['profile_id_by_dx']):
            p,n=decoded[i]
            actual_plus.update((x,50+j) for j in range(400) if p>>j&1)
            actual_minus.update((x,50+j) for j in range(400) if n>>j&1)
        need(actual_plus==positive and actual_minus==negative,('Published correction map mismatch',op))
        corr[op]['all_signed_mask_entries_equal']=True
        # Replacement does not disturb same-row neighboring baseline cells.
        for dx in (-600,1200):
            neighbor=shifted(maps['delay'],x=dx)
            need(not (all_delta & set(neighbor)),('Correction collides with neighbor',op,dx))
    names=('delay','dup','left','right','nand')
    seam_shapes=set();comparisons=0;overlaps=0
    for a in names:
        for b in names:
            for dx in range(-1800,1801,600):
                second=shifted(maps[b],x=dx,y=400)
                common=set(maps[a])&set(second)
                need(all(maps[a][q]==second[q] for q in common),('Vertical conflict',a,b,dx))
                both=black(maps[a])&black(second)
                for x,y in both:
                    need(450<=y<=459,('Seam outside cap',a,b,dx,x,y))
                if common:
                    need(len(common)%43==0 and len(both)*43==len(common)*23,('Unexpected seam ratio',a,b,dx))
                    # Every translated slot seam must have identical local shape.
                    grouped=collections.defaultdict(set)
                    for x,y in both:grouped[x//600].add((x%600,y-400))
                    need(all(len(v)==23 for v in grouped.values()),'Wrong black seam size')
                    seam_shapes.update(tuple(sorted(v)) for v in grouped.values())
                    overlaps+=1
                comparisons+=1
    need(len(seam_shapes)==1,'Seam shapes differ')
    # Black-set rows of anchor define signed coefficients with no lost signs.
    ap=Path('/workspace/shared/report44-recovery-20261004/certificate/data/anchor_patch.json')
    anchor=load(ap)['patch'];seen=set();signed=collections.Counter()
    for a,b,old,new in anchor:
        need((a,b) not in seen,'Duplicate anchor coordinate');seen.add((a,b))
        need(old in (0,1) and new in (0,1) and old!=new,'Invalid anchor flip')
        need(0<=b+144<=220 and 0<=289200-a<=583,'Anchor exponent bounds')
        signed[new-old]+=1
    return dict(operation_minus_two_delays=corr,vertical_comparisons=comparisons,
                nonempty_vertical_overlaps=overlaps,unique_black_seam_shapes=len(seam_shapes),
                seam_black_cells=23,seam_fixed_cells=43,
                anchor=dict(cells=len(anchor),positive=signed[1],negative=signed[-1],sha256=digest(ap)),
                data_sha256=pins)

if __name__=='__main__':
    result=dict(status='PASS_INDEPENDENT_PARTIAL_AUDIT',scope='Occurrence algebra and count, finite motif seams/corrections and anchor support only; full periodic-boundary assembly pending.',
                occurrences=occurrence_counts(),events=polynomial_events(),motifs=motif_checks(),
                checker_sha256=digest(Path(__file__)))
    out=HERE/'receipt.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
