"""Four exact unary-block proofs, from the pinned K218 independent auditor.
Adapted only to remove unrelated imports. Inherited MIT No Attribution license.
"""
def require(ok, message):
    if not ok: raise ValueError(message)

def normalize(word):
    out=[]
    for bit,constant,variable in word:
        if out and out[-1][0]==bit:
            b,c,v=out.pop();out.append((b,c+constant,v+variable))
        else:out.append((bit,constant,variable))
    return out

def exact_blocks(table,stored):
    """Prove the four schemas by literal rows and one explicitly checked self-loop.

    Each token (bit,c,v) has length c+v*n for arbitrary natural n.  The sole
    variable token is traversed by a self-loop, including its n=0 case.
    Remaining tokens are one cell each.  Only represented cells are touched.
    """
    B=[(0,1,0),(1,1,1)];C=[(1,1,0),(0,1,0),(1,0,1)]
    specs=[(73,1,'B','B',[(0,1,0),(1,1,0),(1,0,1)]),
           (95,1,'B','C',[(0,1,0),(1,1,0),(1,0,1)]),
           (48,-1,'B','B',[(1,1,0),(1,0,1),(0,1,0)]),
           (112,-1,'C','B',[(1,0,1),(0,1,0),(1,1,0)])]
    require([(x['entry'],x['direction'],x['before'],x['after'])for x in stored]
         ==[(q,d,a,b)for q,d,a,b,t in specs],'Four block signatures')
    reports=[]
    for rec,(entry,direction,before,after,tokens)in zip(stored,specs):
        target=B if after=='B'else C
        input_word=B if before=='B'else C
        if direction==-1:target=list(reversed(target));input_word=list(reversed(input_word))
        require(normalize(tokens)==normalize(input_word),'Block input word identity')
        q=entry;written=[];trace=[];c=v=0
        for bit,constant,variable in tokens:
            write,move,nxt=table[q,bit]
            require(move==direction,'Block scan direction')
            row=[q,bit,write,move,nxt]
            if variable:
                require((constant,variable)==(0,1)and nxt==q,'Unbounded token is not a self-loop')
                trace.append(['unary',row,[0,0,1]+[0]*10])
            else:
                require(constant==1,'Literal token is not one cell')
                trace.append(['literal',row])
            written.append((write,constant,variable));c+=constant;v+=variable;q=nxt
        require(q==entry and(c,v)==(2,1),'Block state or duration formula')
        require(normalize(written)==normalize(target),'Block output word identity')
        require(rec['steps']=='v+2'and rec['arbitrary_contexts']is True and rec['trace']==trace,
             'Stored block differs from independent exact-row derivation')
        reports.append({'entry':entry,'direction':direction,'before':before,'after':after,
                        'duration':[2,1],'trace':trace,'arbitrary_exterior_untouched':True})
    return reports

