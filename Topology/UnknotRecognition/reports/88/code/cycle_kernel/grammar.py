"""Compositional exact kernels for positive-power expression TREES.

Node tags: leaf, serial, parallel, power. Tree depth/size and every kernel remain
explicit resources. The theorem does not identify an arbitrary compressed graph
with a logarithmic-depth expression.
"""
from .model import Graph,Builder,chain,power_explicit
from .normalize import kernel_power

def parallel(gs):
    b=Builder();left=[];right=[]
    for j,g in enumerate(gs):
        b.add(g,j);left.extend((j,v) for v in g.left);right.extend((j,v) for v in g.right)
    return b.finish(left,right)[0]

def evaluate(tree:dict,k:int=3,*,compress=True,cap=20000,max_depth=64):
    stats={'nodes':0,'power_nodes':0,'max_power_depth':0,'peak_edges':0,'max_width':0}
    def visit(x,depth,powerdepth):
        if depth>max_depth:raise ValueError('expression depth cap')
        if not isinstance(x,dict):raise ValueError('invalid expression node')
        stats['nodes']+=1
        if stats['nodes']>cap:raise ValueError('expression node cap')
        op=x.get('op')
        if op=='leaf':g=Graph.from_dict(x['tile'])
        elif op in ('serial','parallel'):
            children=x['children']
            if not isinstance(children,list) or not children:raise ValueError('empty assembly node')
            gs=[visit(c,depth+1,powerdepth) for c in children]
            g=chain(gs) if op=='serial' else parallel(gs)
        elif op=='power':
            stats['power_nodes']+=1;stats['max_power_depth']=max(stats['max_power_depth'],powerdepth+1)
            child_node=x['child'];n=int(x['exponent_hex'],16);fused=1
            if n<1:raise ValueError('nonpositive exponent')
            # (A^a)^b = A^(ab): do not grow a kernel through redundant powers.
            while isinstance(child_node,dict) and child_node.get('op')=='power':
                z=int(child_node['exponent_hex'],16)
                if z<1:raise ValueError('nonpositive exponent')
                n*=z;fused+=1;stats['nodes']+=1;stats['power_nodes']+=1
                if depth+fused>max_depth or stats['nodes']>cap:raise ValueError('expression resource cap')
                child_node=child_node['child']
            stats['max_power_depth']=max(stats['max_power_depth'],powerdepth+fused)
            child=visit(child_node,depth+fused,powerdepth+fused)
            g=kernel_power(child,n,k)[0] if compress else power_explicit(child,n,cap=cap)
        else:raise ValueError('unknown expression node')
        g.validate_tile()
        if len(g.edges)>cap or g.n>cap:raise ValueError('explicit kernel resource cap; no graph verdict')
        stats['peak_edges']=max(stats['peak_edges'],len(g.edges));stats['max_width']=max(stats['max_width'],len(g.left))
        return g
    return visit(tree,0,0),stats
