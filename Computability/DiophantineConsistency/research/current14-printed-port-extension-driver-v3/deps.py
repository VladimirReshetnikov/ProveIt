"""Exact-path policy for direct dependency output; preserves original lines."""
def need(c,m):
    if not c:raise ValueError(m)

def duplicate(direct,counts,module,path):
    """Record one occurrence; return True only for second identical Init."""
    count=counts.get(module,0)
    if count:
        need(module=='Init' and count==1 and module in direct and direct[module]['path']==str(path),
             ('duplicate or conflicting import',module,str(path)))
    counts[module]=count+1
    return count>0

def validate(lines,direct):
    """Every direct path appears once, except Init may appear exactly twice."""
    by_path={entry['path']:module for module,entry in direct.items()}
    need(len(by_path)==len(direct),'distinct modules share a dependency path')
    counts={}
    for line in lines:
        need(line in by_path,('unrecorded dependency path',line))
        module=by_path[line]
        duplicate(direct,counts,module,line)
    need(set(counts)==set(direct),('missing dependency paths',sorted(set(direct)-set(counts))))
    return counts
