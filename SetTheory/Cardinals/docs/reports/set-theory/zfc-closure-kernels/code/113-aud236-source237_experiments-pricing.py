"""Price alternate logical bases against the exact boundary237 source dictionary.

This deliberately measures source DAGs, not binary states. The full original
macro word is checked against the current expanded AX closed-block word before
any alternative is constructed. No new inference-rule or halting claim.
"""
from pathlib import Path
from functools import cache
import argparse, itertools, json, sys, time

HERE=Path(__file__).resolve().parent
OUTPUT=HERE
import source_core as e
import macro_model as t
OLD_PROGRAM=json.loads((HERE/'original_macro_word.json').read_text())
if isinstance(OLD_PROGRAM,dict):
    OLD_PROGRAM=OLD_PROGRAM['program']
OLD_STACK,_=t.symbolic(OLD_PROGRAM)
OLD_ROWS,BUNDLE=OLD_STACK[1:-1],OLD_STACK[-1]
assert len(OLD_ROWS)==9

@cache
def word(n):
    x=e.S[n]
    if isinstance(x[0],int) and e.closed(x[0]) and e.closed(x[1]):
        return word(x[0])+word(x[1])
    return (n,)

M={166:word(88),121:word(67),168:word(83),171:word(56),
   177:word(108),119:word(77),181:word(96),180:word(78),
   182:word(77)+(41,41,41),218:word(109),178:word(147),
   183:word(111),176:word(80),158:word(28),208:word(46),
   192:(180,),131:(198,),211:(21,),197:(199,)}
def expand(program):return tuple(x for m in program for x in M[m])

assert e.S[275]==(226,274) and e.S[274]==(272,273) and e.S[273]==(202,1)
OLD_WORD=word(226)+word(272)+word(202)
assert expand(OLD_PROGRAM)==OLD_WORD, 'Original macro/current source correspondence failed'
BASE_SET=e.live(e.ROOT)
BASE_STRUCTURES=list(e.S)
DICT={bytes(word(n)):n for n in sorted(BASE_SET) if e.closed(n)}
TRIE={}
for w,n in DICT.items():
    p=TRIE
    for b in w:p=p.setdefault(b,{})
    p[-1]=n

def segment(w,penalty=0):
    """Shortest dictionary-call cover. Only exact contiguous words match."""
    dp=[None]*(len(w)+1);dp[-1]=(0,())
    for i in range(len(w)-1,-1,-1):
        p=TRIE;best=None
        for j in range(i,len(w)):
            if w[j] not in p:break
            p=p[w[j]]
            if -1 in p and dp[j+1] is not None:
                n=p[-1]
                value=1+dp[j+1][0]+penalty*len(e.live(n))
                cand=(value,(n,)+dp[j+1][1])
                if best is None or cand<best:best=cand
        dp[i]=best
    assert dp[0] is not None
    return dp[0][1]

def build(parts):
    """Parenthesize a short segment list, keeping several shape choices."""
    @cache
    def solve(i,j):
        if j==i+1:return (parts[i],)
        opts=[]
        for k in range(i+1,j):
            for a in solve(i,k):
                for b in solve(k,j):
                    n=e.cons(a,b)
                    if e.zero_run(n)>6:continue
                    opts.append(n)
        # Final comparison is complete program DAG count, here retain frontiers
        # in unary-prefix length and full depth to avoid a one-shape collapse.
        uniq={}
        for n in opts:
            key=e.lead(n),e.depth(n)
            old=uniq.get(key)
            sc=(len(e.live(n)-BASE_SET),len(e.live(n)),n)
            if old is None or sc<(len(e.live(old)-BASE_SET),len(e.live(old)),old):uniq[key]=n
        return tuple(sorted(uniq.values(),key=lambda n:(len(e.live(n)-BASE_SET),e.depth(n),e.lead(n),n))[:5])
    return solve(0,len(parts))

def price(program):
    # Throw away per-variant candidate trees; retaining their memoized live
    # sets across hundreds of independent variants needlessly exhausts RAM.
    e.S[:]=BASE_STRUCTURES
    e.I.clear();e.I.update({x:i for i,x in enumerate(e.S)})
    for f in (e.paths,e.boundary,e.live,e.lead,e.zero_run,e.depth):
        f.cache_clear()
    ww=bytes(expand(program));best=None
    for penalty in (0,0.005,0.02):
        parts=segment(ww,penalty)
        # The final escaping break stays rightmost. Its local path is all ones,
        # so reassociation adds no zero ancestor and preserves its break depth.
        for ar in build(parts+(1,)):
            nr=e.replace(e.ROOT,275,ar)
            sc=e.score(nr)
            if sc[1]>6:continue
            row=(sc,len(parts),nr,parts)
            if best is None or row[:2]<best[:2]:best=row
    return best

def export(row,meta,name):
    sc,np,nr,parts=row
    keep=set(e.live(nr));mp={n:i for i,n in enumerate(sorted(keep))}
    db=[tuple(mp[x]for x in e.S[n])if isinstance(e.S[n][0],int)else e.S[n]for n in sorted(keep)]
    (OUTPUT/name).write_text(json.dumps(dict(status='SOURCE_COST_ONLY_UNCOMPILED',
       score=sc,original_nodes=len(BASE_SET),dictionary_calls=np,
       metadata=meta,parts=list(parts),root=mp[nr],structures=db,expanded_source_leaves=len(e.paths(nr))),indent=2)+'\n')

def main():
    global OUTPUT
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=288)
    ap.add_argument('--basis',choices=('ksp','ksq4','ksqdn','ksdne'),default='ksp')
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    OUTPUT=args.output or HERE/('replay_'+args.basis);OUTPUT.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();rows=[];best=None
    baseline=price(OLD_PROGRAM)
    print('BASE',baseline[:2],flush=True)
    export(baseline,{'basis':'old'},'original_reparsed.json')
    for a,b,c in itertools.permutations(('a','b','c')):
        I=t.Imp;axioms={'K':I(a,I(b,a)),
            'S':I(I(a,I(b,c)),I(I(a,b),I(a,c))),
            'T':{'ksp':I(I(I(a,b),a),a),
                 'ksq4':I(t.All(a,b),t.All(a,t.All(a,b))),
                 'ksqdn':I(t.Not(t.Not(t.All(a,b))),t.All(a,b)),
                 'ksdne':I(t.Not(t.Not(a)),a)}[args.basis]}
        for order in itertools.permutations(('K','S','T')):
            for pos in range(8):
                oldrows=OLD_ROWS;rest=oldrows[2:]
                rr=rest[:pos]+[axioms[x]for x in order]+rest[pos:]
                program=[166,121,180,176]+[x for f in rr for x in t.emit(f)]+t.emit(BUNDLE)+t.TAIL
                got,_=t.symbolic(program);assert got==['old_top',oldrows[0],*rr,BUNDLE]
                row=price(program);meta=dict(basis=args.basis,parameters=[a,b,c],order=order,position=pos,macro_count=len(program))
                rows.append(dict(meta,score=row[0],dictionary_calls=row[1]))
                if best is None or row[0]<best:
                    best=row[0];export(row,meta,'best_source.json')
                    print('BEST',len(rows),best,meta,flush=True)
                if len(rows)%12==0:
                    print('PROGRESS',len(rows),round(time.monotonic()-started,2),flush=True)
                    (OUTPUT/'pricing_checkpoint.json').write_text(json.dumps(dict(cases=len(rows),best=best,rows=rows),indent=2)+'\n')
                if len(rows)>=args.limit:break
            if len(rows)>=args.limit:break
        if len(rows)>=args.limit:break
    (OUTPUT/'pricing.json').write_text(json.dumps(dict(status='BOUNDED_SOURCE_DICTIONARY_PRICING',
        baseline_direct_nodes=len(BASE_SET),baseline_reparsed_score=baseline[0],
        original_fine_word_length=len(OLD_WORD),cases=len(rows),best=best,
        seconds=time.monotonic()-started,rows=rows),indent=2)+'\n')

if __name__=='__main__':main()
