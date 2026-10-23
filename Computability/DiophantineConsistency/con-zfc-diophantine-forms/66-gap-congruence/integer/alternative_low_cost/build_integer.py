"""Round9 independently authored degree-separated / two-root composition.

Input JSON and coefficient payloads are inert data. No upstream program is run.
Every named register abbreviates a polynomial, not an extra unknown.
"""
from pathlib import Path
from collections import defaultdict,Counter
import json,gzip,hashlib
ROOT=Path(__file__).resolve().parent
KAPPA=2134940

class Circuit:
    def __init__(self):
        self.nodes=[];self.intern={};self.names={};self.ints={};self.powers={};self.power_plans={}
    def leaf(self,kind,**fields):
        key=(kind,tuple(sorted(fields.items())))
        if key not in self.intern:
            self.intern[key]=len(self.nodes);self.nodes.append(dict(kind=kind,**fields))
        return self.intern[key]
    def c(self,n):
        q=self.leaf('literal',value=n);self.ints[q]=n;return q
    def op(self,kind,a,b):
        ia,ib=self.ints.get(a),self.ints.get(b)
        if ia is not None and ib is not None:
            return self.c(ia+ib if kind=='add' else ia-ib if kind=='sub' else ia*ib)
        if kind=='add':
            if ia==0:return b
            if ib==0:return a
        if kind=='sub':
            if ib==0:return a
            if a==b:return self.c(0)
        if kind=='mul':
            if ia==0 or ib==0:return self.c(0)
            if ia==1:return b
            if ib==1:return a
        if kind in ('add','mul') and a>b:a,b=b,a
        return self.leaf(kind,left=a,right=b)
    def add(self,*args):
        r=self.c(0)
        for a in args:r=self.op('add',r,a)
        return r
    def mul(self,*args):
        r=self.c(1)
        for a in args:r=self.op('mul',r,a)
        return r
    def sub(self,a,b):return self.op('sub',a,b)
    def pow(self,a,n):
        assert isinstance(n,int) and n>=0
        if n==0:return self.c(1)
        ps=self.powers.setdefault(a,{1:a})
        if n not in ps:
            if a in self.power_plans and n in self.power_plans[a]:
                x,y=self.power_plans[a][n];ps[n]=self.mul(self.pow(a,x),self.pow(a,y));return ps[n]
            pairs=[(abs(n-2*k),k) for k in ps if n-k in ps]
            if pairs:
                k=min(pairs)[1];r=self.mul(ps[k],ps[n-k])
            else:
                half=self.pow(a,n//2);r=self.mul(half,half)
                if n%2:r=self.mul(r,a)
            ps[n]=r
        return ps[n]
    def save(self,name,n):self.names[name]=n;return n
    def finish(self,out):
        live=set();todo=[out]
        while todo:
            p=todo.pop()
            if p in live:continue
            live.add(p);n=self.nodes[p]
            if 'left'in n:todo.extend((n['left'],n['right']))
        ids={old:new for new,old in enumerate(sorted(live))};nodes=[]
        for old in sorted(live):
            n=dict(self.nodes[old])
            if 'left'in n:n.update(left=ids[n['left']],right=ids[n['right']])
            nodes.append(n)
        deg=[]
        for n in nodes:
            deg.append(1 if n['kind']=='variable' else 0 if 'left'not in n else
                deg[n['left']]+deg[n['right']] if n['kind']=='mul' else max(deg[n['left']],deg[n['right']]))
        names={k:ids[v] for k,v in self.names.items() if v in ids}
        counts=dict(Counter(n['kind'] for n in nodes if 'left'in n))
        return dict(nodes=nodes,output=ids[out],named_nodes=names,operation_counts=counts,
            total_operations=sum(counts.values()),degree_upper_bound=deg[ids[out]],
            named_degree_bounds={k:deg[v] for k,v in names.items()})

def horner(d,b,items):
    pairs=sorted(items,reverse=True);e,r=pairs[0]
    for f,v in pairs[1:]:r=d.add(d.mul(r,d.pow(b,e-f)),v);e=f
    return d.mul(r,d.pow(b,e))

def records(layout):
    source=json.loads((ROOT/'data'/layout.get('source_file','parent_quartic31.json')).read_text())
    rows=[{tuple(t['powers']):t['coefficient'] for t in q['terms']} for q in source['equations']]
    for dest,src,m in layout.get('source_row_operations',[]):
        for mon,c in rows[src-1].items():rows[dest-1][mon]=rows[dest-1].get(mon,0)+m*c
    for j,sign in enumerate(layout.get('row_orientations',[1]*len(rows))):
        if sign==-1:rows[j]={mon:-c for mon,c in rows[j].items()}
    ans=[];fixed={};sig={}
    for row,target in zip(layout['order'],layout['targets']):
        groups=defaultdict(dict)
        for p,c in rows[row-1].items():
            if c:groups[p[:31]][p[31:]]=c*(2 if sum(p[:31])<2 or 2 in p[:31] else 1)
        for alpha,recipe in sorted(groups.items()):
            items=tuple(sorted(recipe.items()))
            if len(items)==1 and not any(items[0][0]):ref={'literal':items[0][1]}
            else:
                name=sig.setdefault(items,'c%03d'%len(sig));fixed[name]=[{'powers':list(p),'coefficient':c}for p,c in items];ref={'fixed':name}
            ans.append(dict(row=row,target=target,alpha=list(alpha),degree=sum(alpha),
                exponent=target-sum(a*w for a,w in zip(alpha,layout['weights'])),coefficient=ref,recipe=fixed.get(ref.get('fixed'),[{'powers':[0]*4,'coefficient':ref.get('literal')}])))
    return ans,fixed

def build(layout,leadless=True,global_powers=True):
    rec,recipes=records(layout);d=Circuit();A,M,S,P,c,N=d.add,d.mul,d.sub,d.pow,d.c,d.save
    names=['t','g0','h0','k0','l','w','x','y','z','m'];v={s:d.leaf('variable',name=s)for s in names}
    b=N('b',A(M(c(6),v['t']),c(4)));g=N('g',M(b,v['g0']));h=N('h',M(b,v['h0']));k=N('k',M(b,A(M(c(3),v['k0']),c(2))))
    base=N('base',M(d.leaf('fixed',name='radix'),P(b,2)))
    if global_powers:
        W=max(layout['weights']);HH=layout['convolution_height'];required={1,W,W+1,HH+1,W+HH+2,HH+2*W+9}
        for exponents in [layout['weights'],layout['targets']]+[[r['exponent']for r in rec if r['degree']==i]for i in range(3)]:
            exponents=sorted(set(exponents));required.add(exponents[0]);required.update(b-a for a,b in zip(exponents,exponents[1:]))
        todo=required-{0};plan={}
        while len(todo)>1:
            a=max(todo);todo.remove(a);b0=max(todo)
            pairs=[(abs(2*x-a),x,a-x)for x in todo if a-x in todo]
            if pairs:_,x,y=min(pairs)
            elif 2*b0<a:x,y=(a//2,a//2)if a%2==0 else(a-1,1)
            else:x,y=b0,a-b0
            plan[a]=(x,y);todo.update((x,y))
        d.power_plans[base]=plan
    ell=N('ell',horner(d,base,[(w,c(1))for w in layout['weights']]))
    kernels=[]
    for degree in range(3):
        terms=[]
        for r in rec:
            if r['degree']==degree:
                ref=r['coefficient'];node=c(ref['literal'])if'literal'in ref else d.leaf('fixed',name=ref['fixed'])
                terms.append((r['exponent'],node))
        kernels.append(N('Dcode'+str(degree),horner(d,base,terms)))
    word=N('word',A(ell,g));coded=N('coded',A(kernels[0],M(word,A(kernels[1],M(word,kernels[2])))))
    W=max(layout['weights']);HH=layout['convolution_height'];top=P(base,W)
    n0=N('n0',P(base,W+1));nn=N('nn',P(base,W+HH+2))
    targets=N('targets',horner(d,base,[(e,c(1))for e in layout['targets']]))
    mask=N('mask',S(S(n0,c(1)),M(S(b,c(1)),ell)))
    tc0=N('tc_original',A(mask,M(S(base,c(2)),targets,n0)))
    tc=N('tc',S(tc0,c(2)) if leadless else tc0)
    jc=N('jc',A(M(c(2),coded),targets));sc=N('sc',A(g,M(jc,n0)))
    X=N('X',S(S(M(nn,A(sc,tc,c(1))),sc),c(1)) if leadless else A(P(nn,2),M(A(sc,tc),nn),S(S(nn,c(1)),sc)))
    hp=HH+2*W+25
    Y=N('Y',M(d.leaf('fixed',name='threshold'),P(base,hp-16),b));cap=N('cap',M(b,top))
    # Sun/Lucas bridge, using exact division-free half registers.
    L=N('L',M(v['l'],Y));u=N('halfU',M(L,X));U=N('U',M(c(2),u));V=N('V',M(c(4),g,v['w'],Y));ww=N('W',M(b,v['w']))
    ha=N('halfA',M(u,A(V,c(1))));a=N('A',M(c(2),ha));bb=N('B1',A(M(c(2),X),c(1)))
    C=N('C',A(bb,M(S(a,c(2)),h)));ph=N('Phalf',M(u,U,V));pn=N('P',M(c(2),ph))
    K=N('K',A(X,c(1),M(k,S(pn,c(2)))));K2=P(K,2)
    ss=N('S',S(M(c(2),a),c(5)));tt=N('T',A(M(ww,S(M(c(3),C),M(c(2),ww))),c(2)))
    Q=N('Q',A(M(S(P(ph,2),c(1)),K2),c(1)))
    cap3=P(cap,3);g2=P(g,2);diff=N('CKL',S(C,M(K,L)))
    delta=N('Delta',S(M(c(8),cap3,g,K2),M(g2,A(M(c(32),P(diff,2),cap3),M(g2,K2)))))
    xi=N('xi',M(v['z'],v['x']));C2=P(C,2);a2m4=S(P(a,2),c(4))
    D=N('D',A(M(a2m4,C2),c(4)));E=N('E',M(C2,D,xi));fm1=N('Fm1',M(c(4),a2m4,P(E,2)));F=N('F',A(fm1,c(1)))
    G=N('G',S(M(S(ha,c(1)),fm1),c(1)));om=N('Omega',M(c(16),E))
    H=N('H',A(C,M(F,A(S(bb,C),M(om,v['y'])))))
    I=N('I',A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
    sigma=N('Sigma',M(xi,P(ss,5)));rho=N('rho',A(tt,M(ss,v['y'])));ss2=P(ss,2);rho2=P(rho,2)
    theta=N('Theta',M(S(M(rho,S(rho2,ss2)),M(ss2,ss)),A(rho2,M(c(23),ss2))))
    r=N('r',M(b,Q));aa=N('guard',A(r,M(S(M(c(3),delta),c(1)),P(M(r,v['z']),2))))
    dd=N('lucas',M(D,F,I));center=N('center',S(M(sigma,v['m']),theta));sig2=P(sigma,2)
    inner=N('inner',S(P(center,2),M(sig2,A(aa,dd))))
    out=N('F10',S(P(inner,2),M(c(4),P(sig2,2),aa,dd)))
    body=d.finish(out);body.update(schema='round9-split-congruence10-v1',domain='Z',variables=names,base_exponent=KAPPA,leadless=leadless,global_power_planning=global_powers,
        layout_file='data/layout.json',source_proof=layout.get('proof_file','PROOF.md'),fixed_recipes=recipes,popcount_parameter=hp)
    return body,rec

def materialize(recipes,leadless=True):
    ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{n}.bin.gz').read_bytes()),'little')for n in ('beta','K','MC','MF_source')]
    fixed={}
    for name,terms in recipes.items():
        value=0
        for term in terms:
            p=term['coefficient']
            for v,e in zip(ports,term['powers']):p*=v**e
            value+=p
        fixed[name]=value
    fixed.update(radix=1<<KAPPA,threshold=1<<(16*KAPPA-(23 if leadless else 21)))
    out=ROOT/'fixed';out.mkdir(exist_ok=True);manifest=[]
    for n,v in fixed.items():
        raw=abs(v).to_bytes(max(1,(abs(v).bit_length()+7)//8),'little');path=out/(n+'.bin.gz');path.write_bytes(gzip.compress(raw,mtime=0))
        manifest.append(dict(name=n,sign=-1 if v<0 else 1,bits=abs(v).bit_length(),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    (out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')

def main():
    layout=json.loads((ROOT/'data/layout.json').read_text());body,rec=build(layout)
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    (out/'integer10.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    (out/'source_records.json').write_text(json.dumps(rec,indent=2)+'\n')
    metrics={k:v for k,v in body.items()if k not in ('nodes','named_nodes','fixed_recipes')}
    (out/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');materialize(body['fixed_recipes'])
    print(body['total_operations'],body['degree_upper_bound'])
if __name__=='__main__':main()
