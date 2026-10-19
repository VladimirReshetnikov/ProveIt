"""Current dictionary pricing of the Source91 six-DNE bundle family.

This is a new cost integration, not a new Boolean/formalism transformation.
The replacement identity and macro-equivalence obligations are those explicitly
attributed in Source91's dne_calculus_transfer and macro-fine bridge notes.
"""
import json,time
import pricing as p

def is_not(f):return isinstance(f,tuple)and f[0]=='imp'and f[2]==1
def redexes(f,path=()):
    if not isinstance(f,tuple):return []
    return ([path]if is_not(f)and is_not(f[1])else[])+redexes(f[1],path+(1,))+redexes(f[2],path+(2,))
def replace(f,mask,path=()):
    if not isinstance(f,tuple):return f
    if path in mask:
        assert is_not(f)and is_not(f[1])
        return replace(f[1][1],mask,path+(1,1))
    return f[0],replace(f[1],mask,path+(1,)),replace(f[2],mask,path+(2,))

def main():
    p.OUTPUT=p.HERE/'replay_bundle';p.OUTPUT.mkdir(exist_ok=True)
    roots=redexes(p.BUNDLE);assert len(roots)==6
    start=time.monotonic();rows=[];best=None
    for mask in range(64):
        b=replace(p.BUNDLE,{x for i,x in enumerate(roots)if mask>>i&1})
        program=[166,121,180,176]+[x for f in p.OLD_ROWS[1:]for x in p.t.emit(f)]+p.t.emit(b)+p.t.TAIL
        got,_=p.t.symbolic(program);assert got==['old_top',*p.OLD_ROWS,b]
        if mask==0:assert program==p.OLD_PROGRAM
        row=p.price(program);meta=dict(mask=mask,macro_count=len(program),fine_word_length=len(p.expand(program)))
        rows.append(dict(meta,score=row[0],dictionary_calls=row[1]))
        if best is None or row[0]<best:
            best=row[0];p.export(row,meta,'best_source.json')
            print('BEST',best,meta,flush=True)
        if mask%8==7:print('PROGRESS',mask+1,round(time.monotonic()-start,2),flush=True)
    (p.OUTPUT/'pricing.json').write_text(json.dumps(dict(status='BOUNDED_SOURCE_DICTIONARY_PRICING',
        prior_family='Source91 six-DNE bundle masks',redexes=roots,cases=len(rows),best=best,
        seconds=time.monotonic()-start,rows=rows),indent=2)+'\n')

if __name__=='__main__':main()
