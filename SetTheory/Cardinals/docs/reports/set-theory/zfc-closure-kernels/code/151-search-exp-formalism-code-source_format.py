"""Small independent standard-library reader of full binary source trees."""
import json

def read_tree(rows):
    leaves={}
    for path,op,arg in rows:
        assert path and set(path)<={'0','1'}
        assert op in {'CI','CD','CB','CC','CH'}
        assert (op=='CH' and arg is None)or(op!='CH' and type(arg)is int and arg>=0)
        assert path not in leaves
        leaves[path]=(op,arg)
    prefixes={p[:i]for p in leaves for i in range(len(p)+1)}
    def build(p):
        if p in leaves:
            assert p+'0'not in prefixes and p+'1'not in prefixes
            return leaves[p]
        assert p+'0'in prefixes and p+'1'in prefixes
        return(build(p+'0'),build(p+'1'))
    tree=build('');assert write_sites(tree)==rows
    return tree

def is_leaf(t):return isinstance(t[0],str)
def write_sites(t,p=''):
    return [[p,*t]]if is_leaf(t)else write_sites(t[0],p+'0')+write_sites(t[1],p+'1')
def subtree(t,p):
    for b in p:
        assert not is_leaf(t);t=t[int(b)]
    return t
def replace(t,p,new):
    if not p:return new
    b=int(p[0]);r=list(t);r[b]=replace(r[b],p[1:],new);return tuple(r)
def compact(rows):return(json.dumps(rows,separators=(',',':'))+'\n').encode('ascii')
def metrics(t):
    unique=set()
    def walk(n):
        if n in unique:return
        unique.add(n)
        if not is_leaf(n):walk(n[0]);walk(n[1])
    walk(t);rows=write_sites(t)
    return {'dag_nodes':len(unique),'leaf_occurrences':len(rows),'maximum_depth':max(len(p)for p,_,_ in rows),'maximum_zero_run':max(len(run)for p,_,_ in rows for run in p.split('1'))}
