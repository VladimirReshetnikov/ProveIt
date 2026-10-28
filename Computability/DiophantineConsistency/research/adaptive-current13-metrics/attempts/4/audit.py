#!/usr/bin/env python3
"""Exact current13 finite audit. Standard library only; no project imports,
historical program execution, Lean invocation or sampled zero-set argument.
--write materializes only this packet; default/-O compare deterministic bytes.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
LEAN = D/'Lean/DiophantineConsistency'
INPUT_SHA = '51271f7eef8a457e818f74becd16d705dc3506f9772ed9faf7fe18a0485712e3'
SUPPLEMENT_SHA = '6c95029d0866e9f92dfb79417c08f87ad6dc96b5eff3b83acc89b42f142cbd09'
VARS = ['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
PORTS = ['beta','K0','MC','MF']
SYMS = VARS+PORTS
ZERO = (0,)*len(SYMS)
LIMIT = 100000


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2)+'\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    raw = path.read_bytes()
    return {'path':str(path.relative_to(D)), 'sha256':sha(raw), 'bytes':len(raw)}


def read(path):
    return path.read_text()


def authenticate():
    path = HERE/'INPUTS.json'
    need(sha(path.read_bytes()) == INPUT_SHA, 'Frozen pre-execution manifest')
    inputs = json.loads(read(path))
    for r in inputs['files']:
        need(pin(D/r['path']) == r, 'Pinned source/data/accepted endpoint: '+r['path'])
    supplement=HERE/'SUPPLEMENT.json'
    need(sha(supplement.read_bytes())==SUPPLEMENT_SHA, 'Frozen definition supplement')
    for r in json.loads(read(supplement))['files']:
        need(pin(D/r['path'])==r, 'Supplemented exact source '+r['path'])
    need(shutil.disk_usage(HERE).free >= 512*1024**2, '512MiB reserve')
    return inputs


def strip_comments(s):
    out=[]; i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-': depth+=1; i+=2
            elif pair=='-/': depth-=1; i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif pair=='/-': depth=1; i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n': i+=1
        else: out.append(s[i]); i+=1
    need(depth==0, 'Balanced comments')
    return ''.join(out)


def compact(s):
    return re.sub(r'\s+', '', strip_comments(s))


def body(s, name):
    clean=strip_comments(s)
    match=re.search(r'^\s*(?:irreducible_)?def '+re.escape(name)+r'\b(.*?)(?=^\s*(?:private |noncomputable )?(?:theorem|(?:irreducible_)?def|abbrev|instance|end)\b|\Z)', clean, re.M|re.S)
    need(match is not None, 'Unique definition '+name)
    declaration=match[1]
    if ':=' in declaration:
        return declaration.split(':=',1)[1].strip()
    need('→' in declaration and '| ' in declaration, 'Recursive definition '+name)
    return declaration[declaration.index('|'):].strip()


def shape(s, name, expected):
    need(compact(body(s,name)) == compact(expected), 'Actual definition shape '+name)


def region(s, a, b):
    need(s.count(a)==1 and s.count(b)==1, 'Unique delimiters')
    return s.split(a)[1].split(b)[0]


def parse_graph(s):
    aliases=[]
    for line in region(s,'-- BEGIN INPUT ALIASES','-- END INPUT ALIASES').splitlines():
        if not line.strip(): continue
        m=re.fullmatch(r'\s*let (\w+) := (x|ports) (\d+)\s*',line)
        need(m is not None, 'Alias grammar')
        aliases.append([m[1],m[2],int(m[3])])
    rows=[]; known=set(SYMS)
    for line in region(s,'-- BEGIN LITERAL GRAPH','-- END LITERAL GRAPH').splitlines():
        if not line.strip(): continue
        m=re.fullmatch(r'\s*let (\w+) := (\w+) ([*+\-]) (\w+)\s*',line)
        need(m is not None, 'Binary gate grammar')
        name,left,op,right=m.groups()
        def argument(t):
            if t.isdecimal(): return int(t)
            need(t in known, 'Producer before use '+t)
            return t
        a,b=argument(left),argument(right)
        need(name not in known, 'Unique producer')
        rows.append([name,op,a,b]); known.add(name)
    tail=s.split('-- END LITERAL GRAPH')[1].split('\ndef value')[0].strip()
    need(tail.startswith('{ ') and tail.endswith(' }'), 'Record grammar')
    fields=[]
    for part in tail[2:-2].split(', '):
        m=re.fullmatch(r'(\w+):=(\w+)',part)
        need(m is not None, 'Field grammar'); fields.append(list(m.groups()))
    need(re.search(r'def value \(ports : Fin 4 → A\) \(x : Fin 13 → A\) : A := \(core ports x\)\.out',s) is not None,
         'Actual output projection')
    return aliases,rows,fields


FIELDS = ['qm','q','q3','C','E','k','c','a','H','delta','ell','U','Bt','rank','V','y','I','Z','M','W','Dstar','A0','A1','Fs','Fa','out']
FIELD_ALIAS = {'delta':'Delta','rank':'R','y':'g78','out':'P13'}


def graph_check(g, source, parent, page):
    fixed={'schema':'literal_integer_arithmetic_dag_v1','name':'current2011_adaptive13_88_degree51',
           'domain':'strictly positive integers',
           'literal_parent':'candidates/free-j-polarized-positive/source/positive/p13_free_J.json',
           'literal_parent_sha256':'a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8',
           'lean_graph':'../../Lean/DiophantineConsistency/NativeAdaptiveGraph.lean',
           'lean_current':'../../Lean/DiophantineConsistency/NativeAdaptiveCurrent2011.lean',
           'metric_proof':'PROOF.md',
           'scope':'Finite exact schedule/degree/full current ports; existing external Lean positive-zero equivalence, no internal HA/PA/ZFC claim or global minimum'}
    need(all(g.get(n)==v for n,v in fixed.items()), 'Exact domain and theorem/graph metadata')
    need(set(g)==set(fixed)|{'witnesses','fixed_numerals','source','output','operations','operation_breakdown','exact_degree','coefficient_binding'}, 'All graph metadata keys')
    aliases,rows,fields=parse_graph(source)
    need(aliases==[[n,'x',i] for i,n in enumerate(VARS)]+[[n,'ports',i] for i,n in enumerate(PORTS)], 'All17 input aliases')
    need(fields==[[n,FIELD_ALIAS.get(n,n)] for n in FIELDS], 'All26 cut fields')
    need(g['witnesses']==VARS and g['fixed_numerals']==PORTS and g['output']=='P13', '13+4 leaves/output')
    need(rows==g['source']==parent['source'], 'Every ordered paid gate unchanged')
    need(g['coefficient_binding']==page['coefficient_binding'], 'Complete current port metadata')
    need(g['operations']==88 and g['exact_degree']==51 and len(rows)==88, 'Expected metadata, separately proved below')
    counts=dict(Counter(r[1] for r in rows))
    need(counts==g['operation_breakdown']=={'*':48,'+':23,'-':17}, 'Paid operation ledger')
    gates={r[0]:r for r in rows}; live=set()
    def visit(n):
        need(type(n) in (str,int), 'Only integer leaves')
        if type(n) is int or n in live: return
        live.add(n)
        if n in gates:
            visit(gates[n][2]); visit(gates[n][3])
    visit(g['output'])
    need(live==set(gates)|set(SYMS), 'Every88 producer and17 leaf live')
    return {'aliases':aliases,'fields':fields,'ordered_gates':rows,'operations':counts,
            'live_gates':88,'live_unknowns':13,'live_ports':4}


def decoder(text):
    patterns={
        'digit':'A / b ^ k % b','mask':'seed % 2 ^ 636','payload':'seed / 2 ^ 636',
        'discovery':'digit 2 mask j','sigma':'| 0 => 0 | j + 1 => sigma j + discovery j',
        'radix':'(sigma j + 2) ^ (1 - discovery j)',
        'prefixProduct':'| 0 => 1 | j + 1 => prefixProduct j * radix j',
        'mark':'digit 2 mask (430 + q)','tally':'| 0 => 0 | q + 1 => tally q + mark q',
        'flags':'(14 + (mark q : ℤ) * ((digit 16 (payload / prefixProduct 430) (tally q) : ℤ) - 14)).toNat',
        'rawTarget':'(sigma (j + 1) : ℤ) - ((payload / prefixProduct j % radix j : ℕ) : ℤ)',
        'target':'(rawTarget j % 216).toNat',
        'action':'(decide (digit 2 (flags (j / 2)) (2 * (j % 2)) = 1), decide (digit 2 (flags (j / 2)) (2 * (j % 2) + 1) = 1), target j)'}
    for name,want in patterns.items(): shape(text,name,want)
    numeral=body(text,'seed'); need(re.fullmatch(r'\d{715}',numeral) is not None,'Entire715 decimal digits')
    seed=int(numeral); mask=seed % 2**636; payload=seed//2**636
    discovery=[(mask>>j)&1 for j in range(430)]
    sigma=[0]; prefix=[1]; radices=[]
    for j,d in enumerate(discovery):
        radices.append((sigma[j]+2)**(1-d))
        sigma.append(sigma[-1]+d); prefix.append(prefix[-1]*radices[-1])
    flags=[]; tally=0; flag_payload=payload//prefix[-1]
    for q in range(215):
        marked=(mask>>(430+q))&1
        flags.append(14+marked*((flag_payload//16**tally)%16-14))
        tally+=marked
    raw=[sigma[j+1]-(payload//prefix[j])%radices[j] for j in range(430)]
    actions=[[bool((flags[j//2]>>(2*(j%2)))&1),bool((flags[j//2]>>(2*(j%2)+1))&1),raw[j]%216] for j in range(430)]
    need(raw[125]==-1 and [j for j,a in enumerate(actions) if a[2]==215]==[125], 'Actual signed halt125')
    return actions,{'digits':715,'numeral_sha256':sha(numeral.encode()),'discovery':discovery,
                    'sigma':sigma,'prefix_hex':[hex(n) for n in prefix], 'flags':flags,'raw_targets':raw}


TABLE_SHAPES = {
 'headColor':'2 * q + b + 2', 'start':'⟨2, 435, 3, 1⟩',
 'transitionRow':'''let a := action j
  let d := a.2.1.toNat
  (j.val + 1, ⟨(1-d) * rail false a.2.2, headColor (j.val/2) (j.val%2),
    d * rail true a.2.2, a.1.toNat⟩)''',
 'copyRows':'(List.range 2).map (fun b => (433 - 2*a + b, ⟨0,432*a+b,0,432*a+b⟩))',
 'signalRows':'''(targetList d).flatMap (fun q => (List.range 2).map (fun b =>
    (423+2*rail d q+b, ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩)))''',
 'tailRows':'''(List.range 2).flatMap (fun a => (List.range 2).map (fun b =>
    (923+2*a+b, ⟨0,432*a+b,0,438⟩))) ++
  [(927,⟨2,434,2,0⟩),(928,⟨3,436,4,4⟩),(929,⟨4,436,4,0⟩)] ++
  [434,435,436].map (fun t => (496+t,⟨1,438,1,t⟩)) ++
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b =>
    (933+3*a+b,⟨a^2,437,b,437⟩)))''',
 'indexedRows':'[(0, start)] ++ List.ofFn transitionRow ++ (copyRows 0 ++ copyRows 1) ++ (signalRows false ++ signalRows true) ++ tailRows',
 'orderedRows':'[(0, start)] ++ List.ofFn transitionRow ++ (copyRows 1 ++ copyRows 0) ++ (signalRows true ++ signalRows false) ++ tailRows',
 'tile':"(orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)).2",
 'selectorWeight':'1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)',
 'physicalPosition':'''if i.val = 0 then 0 else 1 + ((orderedRows.drop 1).map (fun row =>
    (2 ^ 44 - 1 + selectorWeight row.2 - selectorWeight (tile i)) / 2 ^ 44)).sum'''}


def table_data(decimal, data, table, physical):
    actions,dec=decoder(decimal)
    cached=body(data,'actionCache')
    triples=re.findall(r'\((true|false),\s*(true|false),\s*(\d+)\)',cached)
    residue=re.sub(r'\((true|false),\s*(true|false),\s*(\d+)\)','',cached)
    need(re.fullmatch(r'\s*#\[\s*[,\s]*\]\s*',residue) is not None,'Complete action cache grammar')
    need(actions==[[a=='true',b=='true',int(c)] for a,b,c in triples] and len(actions)==430,'All430 actual actions')
    shape(data,'actionNat','actionCache[j]?.getD (false,false,215)')
    shape(data,'action','actionNat j.val')
    shape(data,'railFormula','205 - 199 * d.toNat + (targets d ∩ Finset.range q).card')
    shape(data,'rail','if _hq : q < 216 then (railCache d)[q]?.getD 0 else railFormula d q')
    targets=[sorted({q for _,direction,q in actions if direction==bool(d)}) for d in (0,1)]
    def arrays(name, marker):
        pat=r'if d then '+marker+r'\[([\d,\s]*)\] else '+marker+r'\[([\d,\s]*)\]'
        m=re.fullmatch(pat,body(data,name)); need(m is not None,'Whole '+name+' grammar')
        return [[int(v) for v in m[k].split(',')] for k in (2,1)]
    need(arrays('targetList','')==targets, 'Both complete target sets')
    rails=[[205-199*d+sum(t<q for t in targets[d]) for q in range(216)] for d in (0,1)]
    need(arrays('railCache','#')==rails, 'All432 rail values including empty q0')
    for name,want in TABLE_SHAPES.items(): shape(table,name,want)
    rows={0:(2,435,3,1)}
    def add(index,tile):
        need(index not in rows,'Unique row index'); rows[index]=tile
    for j,(write,d,q) in enumerate(actions): add(j+1,((1-d)*rails[0][q],2*(j//2)+j%2+2,d*rails[1][q],int(write)))
    for a in range(2):
        for b in range(2): add(433-2*a+b,(0,432*a+b,0,432*a+b))
    for d in range(2):
        for q in targets[d]:
            for b in range(2): add(423+2*rails[d][q]+b,(d*rails[d][q],b,(1-d)*rails[d][q],2*q+b+2))
    for a in range(2):
        for b in range(2): add(923+2*a+b,(0,432*a+b,0,438))
    for i,t in [(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))]: add(i,t)
    for t in (434,435,436): add(496+t,(1,438,1,t))
    for a in range(3):
        for b in range(3): add(933+3*a+b,(a*a,437,b,437))
    need(sorted(rows)==list(range(942)) and len(set(rows.values()))==942,'Complete942 distinct table')
    tiles=[rows[i] for i in range(942)]
    need(all(w<256 and n<512 and e<256 and s<512 for w,n,e,s in tiles),'All true color bounds')
    weights=[1+2**10*(1+w+2**8*n+2**17*e+2**25*s) for w,n,e,s in tiles]
    order=[0]+sorted(range(1,942),key=lambda i:-weights[i]); positions=[0]*942
    need(len(set(weights))==942 and max(weights)<2**44,'Distinct bounded weights')
    for p,i in enumerate(order): positions[i]=p
    for i in range(1,942):
        rank=1+sum((2**44-1+weights[j]-weights[i])//2**44 for j in range(1,942))
        need(positions[i]==rank,'Every printed physical floor rank')
    blocks=re.findall(r'def chunk(\d{2}) : List \(ℕ × ℕ\) := \[([^\]]*)\]',physical,re.S)
    need([int(n) for n,_ in blocks]==list(range(59)),'All59 physical chunks')
    actual=[]
    for n,b in blocks:
        pairs=re.findall(r'\((\d+),\s*(\d+)\)',b)
        need(re.fullmatch(r'[,\s]*',re.sub(r'\((\d+),\s*(\d+)\)','',b)) is not None,'Physical data grammar')
        need(len(pairs)==(16 if int(n)<58 else 13),'Physical chunk lengths')
        actual.extend((int(a),int(w)) for a,w in pairs)
    need(re.findall(r'chunk\d{2}',body(physical,'rows'))==['chunk'+str(i).zfill(2) for i in range(59)],'Physical concatenation')
    need(actual==[(i,weights[i]) for i in order[1:]],'All941 physical index/weight entries')
    need(positions[928]==504,'Actual initializer928 rank504')
    coeff=[0]*3297
    for i,w in enumerate(weights): coeff[positions[i]]+=2*w
    for n,p,e in [(8,978,10),(9,960,18),(8,969,27),(9,942,35)]:
        for j in range(n): coeff[p+j]+=2**(e+j+1)
    return coeff,{'decoder':dec,'actions':actions,'target_lists':targets,'rails':rails,
                  'indexed_tiles':[[i,*tiles[i]] for i in range(942)],'abstract_weights':weights,
                  'physical_order':order,'physical_positions':positions,'all3297_coefficients':coeff}


def owner_shapes(mask,kernel):
    for n,e in {'radix':'2 ^ 47','width':'47 * 2011','beta':'radix ^ 2011 - 1',
                'lowSupport':'Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}',
                'lowPort':'mask radix 2 2011 lowSupport',
                'highPrefix':'4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++ List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4])',
                'highDigits':'highPrefix ++ List.replicate 1005 0',
                'highPort':'Nat.ofDigits radix highDigits','ports':'![beta, K, lowPort, highPort + beta]'}.items(): shape(mask,n,e)
    shape(kernel,'position','''| .inl i => physicalPosition i
  | .inr (.inl j) => 978 + j.val
  | .inr (.inr (.inl j)) => 960 + j.val
  | .inr (.inr (.inr (.inl j))) => 969 + j.val
  | .inr (.inr (.inr (.inr j))) => 942 + j.val''')
    shape(kernel,'weight','''| .inl i => selectorWeight (tile i)
  | .inr (.inl j) => 2 ^ (10 + j.val)
  | .inr (.inr (.inl j)) => 2 ^ (18 + j.val)
  | .inr (.inr (.inr (.inl j))) => 2 ^ (27 + j.val)
  | .inr (.inr (.inr (.inr j))) => 2 ^ (35 + j.val)''')
    shape(kernel,'exponent','| .inl j => ![18, 1004, 2020] j | .inr e => 1005 - position e')
    shape(kernel,'coefficient','| .inl _ => 1 | .inr e => 2 * weight e')
    shape(kernel,'rawWord','∑ t : Term, coefficient t * r ^ exponent t')
    shape(kernel,'K','rawWord radix')


def compressed_port(compressed,raw,entry):
    need(gzip.decompress(compressed)==raw, 'Every decompressed coefficient byte')
    need(sha(compressed)==entry['gzip_sha256'], 'Complete deterministic compressed bytes')


def whole_ports(coeff):
    need(len(coeff)==3297 and all(type(n) is int and n>=0 for n in coeff),'Coefficient types/length')
    need(all(e<=1005 for e,n in enumerate(coeff) if n),'No truncated negative reflection')
    powr=lambda e:1<<(47*e)
    geom=lambda n:sum(powr(j) for j in range(n))
    beta=powr(2011)-1
    K=powr(18)+powr(1004)+powr(2020)+sum(n*powr(1005-e) for e,n in enumerate(coeff) if n)
    support=list(range(951))+list(range(960,986))+[1004]
    MC=beta-sum(powr(e) for e in support)
    digits=[4]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005
    need(len(digits)==2011 and len(support)==978,'Exact mask lengths')
    high=sum(n*powr(e) for e,n in enumerate(digits) if n)
    direct=8*geom(917)-4+(2**45-4)*powr(1005)+powr(960)*geom(9)+powr(987)*geom(8)+powr(1004)
    need(high==direct and MC==beta-geom(951)-powr(960)*geom(26)-powr(1004),'Both whole mask routes')
    need(0<MC<beta<beta+high<2*beta and MC%4==2,'Actual scalar boxes and origin residues')
    return dict(zip(PORTS,[beta,K,MC,beta+high]))


def compare_ports(g, values, coeff):
    native=D/'research/padding-staircase-independent'
    need(coeff==json.loads(read(native/'coefficients.json')),'All3297 frozen array entries')
    cert=json.loads(read(native/'certificate.json')); records={}
    for name,n in values.items():
        raw=n.to_bytes((n.bit_length()+7)//8,'big'); r={'bits':n.bit_length(),'bytes':len(raw),'sha256':sha(raw)}
        alias={'K0':'K','MF':'MF_source'}.get(name,name)
        need(r==cert['constant_ports'][alias],'Full native port '+name)
        entry=g['coefficient_binding']['ports'][name]
        compressed=(HERE/'coefficients'/entry['file']).read_bytes()
        original=(D/'candidates/one-page-padding-staircase-carrier65-2011/coefficients'/entry['file']).read_bytes()
        need(compressed==original,'Every original compressed byte '+name)
        compressed_port(compressed,raw,entry)
        need(r=={'bits':entry['bits'],'bytes':entry['raw_bytes'],'sha256':entry['raw_sha256']},'Whole port binding '+name)
        records[name]=r
    need(sum(r['bytes'] for r in records.values())==47313==g['coefficient_binding']['raw_bytes'],'All47313 raw bytes')
    return {'records':records,'raw_bytes':47313,'MF_shifted_exactly_once':True}


def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if out[m]==0: del out[m]
    need(len(out)<=LIMIT,'Sparse term reserve')
    return out


def mul(a,b):
    need(len(a)*len(b)<=5000000,'Bounded product pairs')
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb)); out[m]=out.get(m,0)+ca*cb
    out={m:c for m,c in out.items() if c}
    need(len(out)<=LIMIT,'Sparse term reserve')
    return out


def const(n): return {ZERO:n} if n else {}
def symbol(n):
    m=list(ZERO); m[SYMS.index(n)]=1; return {tuple(m):1}
def powp(p,n):
    out=const(1)
    for _ in range(n): out=mul(out,p)
    return out
def prod(*factors):
    out=const(1)
    for f in factors: out=mul(out,f)
    return out
def degree(p): return max((sum(m[:13]) for m in p),default=-1)
def leading(p):
    d=degree(p); return {m:c for m,c in p.items() if sum(m[:13])==d}
def prows(p): return [[list(m),c] for m,c in sorted(p.items())]


def exact_evaluator(graph):
    cache={n:symbol(n) for n in SYMS}; gates={r[0]:r for r in graph['source']}
    def get(n):
        if type(n) is int: return const(n)
        if n not in cache:
            _,op,l,r=gates[n]; a,b=get(l),get(r)
            cache[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        return cache[n]
    return get


def check_cancellations(g):
    full=exact_evaluator(g); get=full
    M,ell,k,r,Y,qm,Bt,W,q3=[get(n) for n in ('M','ell','k','r','Y','qm','Bt','W','q3')]
    h=add(add(mul(M,add(k,r)),mul(Y,qm)),prod(Bt,W,q3),-1)
    need(get('Z')==add(mul(M,ell),h),'Actual first-root split')
    alt0=add(add(add(prod(const(2),M,ell,h),powp(h,2)),prod(powp(M,2),ell,k),-1),powp(M,2),-1)
    U,a,c,X,H,shift=[get(n) for n in ('U','a','c','X','H','shift')]
    v=add(mul(U,X),mul(H,shift))
    need(get('Dstar')==add(prod(U,a,c),v) and get('Delta')==add(powp(a,2),H),'Actual main-root split')
    alt1=add(add(add(prod(const(2),U,a,c,v),powp(v,2)),prod(powp(U,2),H,powp(c,2)),-1),powp(U,2),-1)
    V,u=get('V'),get('u'); alt81=add(prod(const(2),V,u),powp(u,2))
    alternates={'A0':alt0,'A1':alt1,'g81':alt81}; result={}
    for n,alt in alternates.items():
        need(get(n)==alt,'Full polynomial cancellation '+n)
        result[n]={'identity_verified':True,'full_terms':len(alt),'full_polynomial_sha256':sha(encoded(prows(alt))),
                   'exact_degree':degree(alt),'complete_leader':prows(leading(alt))}
    need([result[n]['exact_degree'] for n in ('A0','A1','g81')]==[15,13,7],'Sharp cancellation degrees')
    return full,result


def specialized(p,ports,mod):
    out={}
    for m,c in p.items():
        for i,n in enumerate(PORTS): c=c*pow(ports[n]%mod,m[13+i],mod)%mod
        key=m[:13]; out[key]=(out.get(key,0)+c)%mod
    return {m:c for m,c in out.items() if c}


def check_degree(g,ports):
    full,cancel=check_cancellations(g)
    leaders={s:symbol(s) for s in SYMS}; records={}; zero_leaders=[]
    for n,op,l,r in g['source']:
        a=const(l) if type(l) is int else leaders[l]
        b=const(r) if type(r) is int else leaders[r]
        if op=='*': p=mul(a,b)
        elif degree(a)>degree(b): p=a
        elif degree(a)<degree(b): p=b if op=='+' else mul(const(-1),b)
        else: p=add(a,b,1 if op=='+' else -1)
        if not p:
            zero_leaders.append(n); need(n in cancel,'Unexpected leading cancellation '+n)
            p=leading(full(n))
        need(bool(p),'Every formal gate has nonzero leader'); leaders[n]=p
        witness=None
        for mod in (1000003,1000033,1000037):
            actual=specialized(p,ports,mod)
            if actual:
                mon=min(actual); witness={'modulus':mod,'unknown_monomial':list(mon),'coefficient':actual[mon],
                    'full_specialized_leader_modulus':prows(actual)}; break
        need(witness is not None,'Actual specialized degree witness '+n)
        records[n]={'degree':degree(p),'complete_formal_leader':prows(p),'specialized_nonzero':witness}
    need(zero_leaders==['A0','A1','g81'],'Exactly three literal leading cancellations')
    q0=mul(symbol('beta'),symbol('J')); k0=add(symbol('eta'),symbol('zeta'))
    R0=mul(powp(q0,3),add(q0,symbol('F'),-1))
    Bt0=add(mul(add(mul(symbol('K0'),q0),symbol('X')),add(add(q0,symbol('F'),-1),symbol('alpha'),-1)),mul(q0,symbol('F')),-1)
    X,Y,f,i,u,ga=[symbol(n) for n in ('X','Y','f','i','u','gamma')]
    factors={
      'F0':prod(const(-2),powp(q0,8),powp(k0,2),X,powp(Y,2),Bt0),
      'F1':prod(const(8),powp(q0,2),k0,powp(X,2),powp(Y,4),add(prod(powp(q0,2),Y,ga),R0)),
      'Fa':prod(const(2),powp(X,2),powp(Y,2),powp(f,4),u,R0),
      'Fs':prod(powp(i,2),powp(k0,4),powp(Y,4))}
    need(all(leaders[n]==p for n,p in factors.items()),'Independent four complete factor leaders')
    expected=prod(*(factors[n] for n in ('F0','F1','Fa','Fs')))
    need(leaders['P13']==expected and degree(expected)==51,'Complete output degree51 leader')
    chosen={'J':15,'F':1,'eta':7,'X':6,'Y':13,'f':4,'i':2,'u':1,'gamma':1,'alpha':1}
    mon=tuple(chosen.get(n,0) for n in VARS)
    coeff={m[13:]:c for m,c in expected.items() if m[:13]==mon}
    need(coeff=={(15,0,0,0):-32},'Exact selected coefficient is -32*beta^15 independently of other ports')
    magnitude=32*ports['beta']**15
    raw=magnitude.to_bytes((magnitude.bit_length()+7)//8,'big')
    return {'symbols':SYMS,'cancellations':cancel,'all_gate_leaders':records,
            'factor_degrees':{n:degree(p) for n,p in factors.items()},'complete_output_leader':prows(expected),
            'exact_degree':51,'selected_unknown_monomial':chosen,'selected_coefficient':'-32*beta^15',
            'actual_selected_coefficient':{'sign':-1,'nonzero':ports['beta']>0,'bits':magnitude.bit_length(),'bytes':len(raw),'sha256_magnitude':sha(raw)}}


def scalar(g,inputs,mod):
    env={n:v%mod for n,v in inputs.items()}
    for n,op,l,r in g['source']:
        a=l if type(l) is int else env[l]; b=r if type(r) is int else env[r]
        env[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
    return env[g['output']]


def dependence(g,ports):
    mod=1000003; result={}
    for n in SYMS:
        for base in range(1,12):
            inputs=dict(ports,**{v:base for v in VARS}); changed=dict(inputs); changed[n]+=1
            a,b=scalar(g,inputs,mod),scalar(g,changed,mod)
            if a!=b:
                result[n]={'all_unknowns_before':base,'increment':1,'before':a,'after':b}; break
        need(n in result,'Genuine dependence '+n)
    return {'modulus':mod,'actual_port_residues':{n:v%mod for n,v in ports.items()},'witnesses':result,
            'scope':'Unequal exact modular evaluations certify dependence, not zero-set equivalence.'}


def negative_controls(g,source,parent,page,texts,coeff,values):
    rejected=[]
    def reject(label,check):
        try: check()
        except (ValueError,KeyError): rejected.append(label)
        else: raise ValueError('Undetected actual corruption '+label)
    for j,(n,op,l,r) in enumerate(g['source']):
        old=f'  let {n} := {l} {op} {r}'
        for label,new in [('operator',f'  let {n} := {l} '+{'*':'+','+':'-','-':'+'}[op]+f' {r}'),('operand',f'  let {n} := 0 {op} {r}')]:
            bad=source.replace(old,new,1); need(bad!=source,'Changed real gate')
            reject(f'gate-{j}-{label}',lambda bad=bad:graph_check(g,bad,parent,page))
    aliases,_,fields=parse_graph(source)
    for n,kind,j in aliases:
        bad=source.replace(f'let {n} := {kind} {j}',f'let {n} := {kind} {(j+1)%(13 if kind=="x" else 4)}',1)
        reject('alias-'+n,lambda bad=bad:graph_check(g,bad,parent,page))
    for n,p in fields:
        bad=source.replace(n+':='+p,n+':='+('qm' if p!='qm' else 'q'),1)
        reject('field-'+n,lambda bad=bad:graph_check(g,bad,parent,page))
    bad=source.replace('(core ports x).out','(core ports x).A0',1)
    reject('output-projection',lambda:graph_check(g,bad,parent,page))
    for name in ('count','degree','extra-variable','rational','dead-gate','port-shift','domain','theorem-path'):
        b=deepcopy(g)
        if name=='count': b['operations']=87
        elif name=='degree': b['exact_degree']=50
        elif name=='extra-variable': b['witnesses'].append('unused')
        elif name=='rational': b['source'][0][2]=0.5
        elif name=='dead-gate': b['source'].append(['dead','+',1,1])
        elif name=='port-shift': b['coefficient_binding']['ports']['MF']['bits']-=1
        elif name=='domain': b['domain']='all signed integers'
        else: b['lean_current']='unrelated.lean'
        reject('metadata-'+name,lambda b=b:graph_check(b,source,parent,page))
    mask,kernel=texts['mask'],texts['kernel']
    for name,old,new,which in [('mask-marker','{1004}','{1003}','mask'),('dummy-support','Ico 960 986','Ico 960 985','mask'),
      ('padding-bit','916 8','916 4','mask'),('origin','4 ::','8 ::','mask'),
      ('double-shift','highPort + beta','highPort + beta + beta','mask'),('kernel-center','1005 -','1004 -','kernel'),
      ('kernel-scale','2 * weight','1 * weight','kernel'),('kernel-marker','18, 1004, 2020','18, 1003, 2020','kernel'),
      ('control-direction','978 + j.val','969 + j.val','kernel')]:
        altered=texts[which].replace(old,new,1); need(altered!=texts[which],'Actual data mutation')
        reject(name,lambda altered=altered,which=which:owner_shapes(altered if which=='mask' else mask,altered if which=='kernel' else kernel))
    for name,index in [('selector',0),('label',978),('zero-dummy',977),('out-of-band',1006)]:
        bad=list(coeff); bad[index]+=1
        reject('array-'+name,lambda bad=bad:compare_ports(g,whole_ports(bad),bad))
    for name in PORTS:
        wrong=dict(values); wrong[name]+=1
        reject('whole-port-byte-'+name,lambda wrong=wrong:compare_ports(g,wrong,coeff))
        raw=values[name].to_bytes((values[name].bit_length()+7)//8,'big')
        changed=bytearray(raw); changed[len(changed)//2]^=1
        compressed=gzip.compress(bytes(changed),mtime=0)
        entry=g['coefficient_binding']['ports'][name]
        reject('compressed-payload-'+name,lambda compressed=compressed,raw=raw,entry=entry:compressed_port(compressed,raw,entry))
    wrong=dict(values); wrong['MF']+=values['beta']
    reject('whole-MF-duplicate-shift',lambda:compare_ports(g,wrong,coeff))
    for label,which,old,new in [
        ('target-modulus','decimal','rawTarget j % 216','rawTarget j % 215'),
        ('flag-bit','decimal','2 * (j % 2) + 1','2 * (j % 2) + 2'),
        ('action-write','data','(true, true, 1)','(false, true, 1)'),
        ('rail-origin','data','then #[6, 7','then #[7, 7'),
        ('Start-color','table','⟨2, 435, 3, 1⟩','⟨2, 435, 3, 0⟩'),
        ('physical-weight','physical','(926, 15049678914561)','(926, 15049678914562)'),
        ('physical-coverage','physical','chunk00 ++','chunk01 ++')]:
        altered=dict(texts); altered[which]=texts[which].replace(old,new,1)
        need(altered[which]!=texts[which], 'Actual table/decoder corruption '+label)
        reject(label,lambda altered=altered:table_data(altered['decimal'],altered['data'],altered['table'],altered['physical']))
    seed=body(texts['decimal'],'seed'); changed=seed[:-1]+str((int(seed[-1])+1)%10)
    altered=texts['decimal'].replace(seed,changed,1)
    reject('actual-decimal-digit',lambda:table_data(altered,texts['data'],texts['table'],texts['physical']))
    return rejected


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--write',action='store_true'); args=parser.parse_args()
    inputs=authenticate(); g=json.loads(read(HERE/'polynomial.json'))
    parent=json.loads(read(D/'candidates/free-j-polarized-positive/source/positive/p13_free_J.json'))
    page=json.loads(read(D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'))
    source=read(LEAN/'NativeAdaptiveGraph.lean')
    graph=graph_check(g,source,parent,page)
    texts={k:read(LEAN/(n+'.lean')) for k,n in [('decimal','DecimalMachine215'),('data','WangTiles942Data'),
      ('table','WangTiles942TableData'),('physical','WangTiles942PhysicalData'),('mask','CurrentMaskData2011'),('kernel','CurrentKernelData2011')]}
    low=read(LEAN/'LowMaskData.lean')
    shape(low,'supportValue','∑ j ∈ S, B ^ j')
    shape(low,'mask','B ^ len - 1 - (b-1) * supportValue B S')
    coeff,table=table_data(texts['decimal'],texts['data'],texts['table'],texts['physical'])
    owner_shapes(texts['mask'],texts['kernel']); values=whole_ports(coeff); ports=compare_ports(g,values,coeff)
    degrees=check_degree(g,values); deps=dependence(g,values)
    mutations=negative_controls(g,source,parent,page,texts,coeff,values)
    certificate={'schema':'adaptive_current13_metrics_v1','status':'PASS','input_manifest':pin(HERE/'INPUTS.json'),
      'definition_supplement':pin(HERE/'SUPPLEMENT.json'),
      'auditor':pin(Path(__file__)),'graph_pin':pin(HERE/'polynomial.json'),'metric_proof':pin(HERE/'PROOF.md'),
      'graph':graph,'table_data':table,'ports':ports,'degree':degrees,'actual_dependence':deps,'rejected_mutations':mutations,
      'scope':'Finite exact current13 schedule/whole ports/every gate leader/degree51; existing pinned external Lean equivalence. No new Lean build, internal HA/PA/ZFC claim or global minimum.'}
    authenticate(); payload=encoded(certificate); target=HERE/'CERTIFICATE.json'
    if args.write: target.write_bytes(payload)
    else: need(target.read_bytes()==payload,'Complete deterministic certificate bytes')
    print(json.dumps({'status':'PASS','operations':88,'variables':13,'degree':51,'raw_port_bytes':47313,
                     'mutations':len(mutations),'certificate':pin(target)},sort_keys=True,indent=2))


if __name__=='__main__': main()
