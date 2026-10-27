#!/usr/bin/env python3
"""Bounded homogeneous-layer search, no equation/source materialization.
All graph rows are assembled in memory from a pinned literal parent.
Standard library only; no project or incoming program is imported.
"""
from pathlib import Path
import hashlib,json
from collections import Counter
HERE=Path(__file__).resolve().parent
PIN='48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1'
raw=(HERE.parent/'thirteen-unit-sphere96/polynomial.json').read_bytes()
def require(b,m):
    if not b:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
require(sha(raw)==PIN,'complete parent pin')
g=json.loads(raw);syms=g['witnesses']+g['fixed_numerals'];zero=(0,)*17

def C(n):return {zero:n} if n else {}
def X(s):
    m=list(zero);m[syms.index(s)]=1;return {tuple(m):1}
def degree(p):return max((sum(m[:13]) for m in p),default=-1)
def add(a,b,sign=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sign*c
    return {m:c for m,c in r.items() if c}
def mul(a,b,cut=-1):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            q=tuple(x+y for x,y in zip(m,n))
            if sum(q[:13])>=cut:r[q]=r.get(q,0)+c*d
    return {m:c for m,c in r.items() if c}
def rows(p):return [[list(m),c] for m,c in sorted(p.items())]
def full(n,cache,S):
    if type(n)is int:return C(n)
    if n not in cache:
        _,op,l,r=S[n];a=full(l,cache,S);b=full(r,cache,S)
        cache[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    return cache[n]

# 17 extra paid operations. Existing f^2-1, G, V, C and R are reused.
# W=b*T*G*V, coefficient=16*W*(W*(f²-1)+2*f²*T*(V*C-b*f²*G*R)).
def candidate(bname, third=False):
    extra=[['bG','*',bname,'B'],['bGT','*','bG','T'],['WG','*','bGT','V'],
      ['WGh','*','WG','f2minus1'],['VC','*','V','C'],['bGf2','*','bG','f2'],
      ['bGf2R','*','bGf2','R'],['gap2','-','VC','bGf2R'],['f2T','*','f2','T'],
      ['term2','*','f2T','gap2'],['twoterm2','*',2,'term2'],['bracket','+','WGh','twoterm2'],
      ['coeff0','*','WG','bracket'],['coeff','*',16,'coeff0'],['Pminus1','-','N0',1],
      ['correction','*','coeff','Pminus1'],['correctedU','-','Na','correction']]
    if third is True:
        more=[['XC','*','X','C'],['D3','-','XC','bG'],['f2T2','*','f2T','T'],
              ['f2T2V','*','f2T2','V'],['f2T2VVC','*','f2T2V','VC'],
              ['coef3pre','*','f2T2VVC','D3'],['coef3','*',32,'coef3pre'],
              ['coeffFinal','-','coeff','coef3']]
        extra=extra[:14]+more+extra[14:]
        for r in extra:
            if r[0]=='correction':r[2]='coeffFinal'
    if third=='shared':
        extra=[['bG','*',bname,'B'],['bGT','*','bG','T'],['WG','*','bGT','V'],
          ['WG2','*','WG','WG'],['WG2h','*','WG2','f2minus1'],['VC','*','V','C'],
          ['bGf2','*','bG','f2'],['bGf2R','*','bGf2','R'],['gap2','-','VC','bGf2R'],
          ['XC','*','X','C'],['D3','-','XC','bG'],['TV','*','T','V'],['TVVC','*','TV','VC'],
          ['termD','*','TVVC','D3'],['WGgap','*','WG','gap2'],['diffcorr','-','WGgap','termD'],
          ['f2T','*','f2','T'],['prod','*','f2T','diffcorr'],['two','*',2,'prod'],
          ['bracket','+','WG2h','two'],['coeff','*',16,'bracket'],['Pminus1','-','N0',1],
          ['correction','*','coeff','Pminus1'],['correctedU','-','Na','correction']]
    if third=='factored':
        extra=[['bG','*',bname,'B'],['bG2','*','bG','bG'],['Vh','*','V','f2minus1'],
          ['firstterm','*','bG2','Vh'],['VC','*','V','C'],['XC','*','X','C'],
          ['twoBG','*',2,'bG'],['gap3','-','twoBG','XC'],['VCgap','*','VC','gap3'],
          ['f2R','*','f2','R'],['bG2f2R','*','bG2','f2R'],['inner3','-','VCgap','bG2f2R'],
          ['f2inner3','*','f2','inner3'],['twoinner3','*',2,'f2inner3'],
          ['bracket','+','firstterm','twoinner3'],['T2','*','T','T'],['T2V','*','T2','V'],
          ['coeff0','*','T2V','bracket'],['coeff','*',16,'coeff0'],['Pminus1','-','N0',1],
          ['correction','*','coeff','Pminus1'],['correctedU','-','Na','correction']]
    source=g['source'][:68]+extra+[r[:]for r in g['source'][68:]]
    for r in source:
        if r[0]=='sqU':r[2]=r[3]='correctedU'
    return source,extra

def audit(bname,third=False):
    source,extra=candidate(bname,third);S={r[0]:r for r in source}
    require(len(S)==len(source)==(97 if third=='factored' else 99 if third=='shared' else 100 if third else 92),'all distinct paid operations')
    fullQ=full('N1',{s:X(s) for s in syms},S)
    require(degree(fullQ)==18 and len(fullQ)==323,'full Q')
    # The six highest drops are retained through every pre-correction gate.
    # After its first sharp leader is recovered only that leader is used.
    width=6;cache={s:(1 if s in g['witnesses'] else 0,X(s)) for s in syms}
    leaderU=None;boundU=None;degrees={}
    for n,op,l,r in source:
        da,a=(0,C(l)) if type(l)is int else cache[l]
        db,b=(0,C(r)) if type(r)is int else cache[r]
        bound=da+db if op=='*' else max(da,db)
        p=mul(a,b,bound-width) if op=='*' else add(a,b,1 if op=='+' else -1)
        p={m:c for m,c in p.items() if sum(m[:13])>=bound-width}
        if n=='N1':bound=18;p={m:c for m,c in fullQ.items() if sum(m[:13])>=18-width}
        if n=='D3':
            p=full(n,{s:X(s) for s in syms},S);bound=degree(p)
            require(bound==2,'exact XC-bG cancellation')
        if n=='correctedU':
            require(bound==48 and p,'nonzero retained correction layer')
            bound=degree(p);p={m:c for m,c in p.items() if sum(m[:13])==bound}
            leaderU=p;boundU=bound
        if n in ('sqU','sumPQ_U','sumSquares','polynomial'):
            p={m:c for m,c in p.items() if sum(m[:13])==bound}
        require(p and degree(p)==bound,'sharp bound '+n)
        cache[n]=(bound,p);degrees[n]=bound
    live=set()
    def visit(n):
        if type(n)is int or n in live:return
        live.add(n)
        if n in S:visit(S[n][2]);visit(S[n][3])
    visit('polynomial');require(live==set(syms)|set(S),'all rows/leaves live')
    require(cache['polynomial'][1]==mul(leaderU,leaderU),'whole output leader')
    return {'b_factor':bname,'third_correction':third,'paid_operations':dict(Counter(r[1] for r in source)),
      'paid_total':len(source),'auxiliary_degree':boundU,'output_degree':cache['polynomial'][0],
      'auxiliary_leader':rows(leaderU),'output_leader_terms':len(cache['polynomial'][1]),
      'output_leader_sha256':sha(json.dumps(rows(cache['polynomial'][1]),sort_keys=True).encode()),
      'extra_rows':extra,'all_gate_degrees':degrees}

out={'scope':'bounded exploratory calculation; no new candidate/Lean theorem or global minimum',
     'script_sha256':sha(Path(__file__).read_bytes()),'parent_sha256':PIN,
     'variants':[audit('qm'),audit('q'),audit('qm',True),audit('qm','shared'),audit('qm','factored')]}
require(out['variants'][2]['auxiliary_leader']==out['variants'][3]['auxiliary_leader'],
        'literal refactoring has same full leader')
# Independent cut-polynomial equality of the two coefficient schedules.
# Every cut is an actual common producer or coordinate, not a guessed output.
cutnames=['WG','f2minus1','f2T','gap2','T','V','VC','D3']
cutcache={n:X(syms[i]) for i,n in enumerate(cutnames)}
oldrows,_=candidate('qm',True);newrows,_=candidate('qm','shared')
old=full('coeffFinal',dict(cutcache),{r[0]:r for r in oldrows})
new=full('coeff',dict(cutcache),{r[0]:r for r in newrows})
require(old==new,'whole coefficient refactoring identity')
out['shared_coefficient_cut_identity_terms']=len(old)
cutnames2=['bG','T','V','f2minus1','C','X','f2','R']
cutcache2={n:X(syms[i]) for i,n in enumerate(cutnames2)}
newestrows,_=candidate('qm','factored')
oldfull=full('coeffFinal',dict(cutcache2),{r[0]:r for r in oldrows})
newfull=full('coeff',dict(cutcache2),{r[0]:r for r in newestrows})
require(oldfull==newfull,'complete factored coefficient equality')
require(out['variants'][2]['auxiliary_leader']==out['variants'][4]['auxiliary_leader'],
        'complete factored leader unchanged')
out['factored_coefficient_identity_terms']=len(newfull)
print(json.dumps(out,indent=2,sort_keys=True))
