"""Small integral coordinates on an affine hyperplane; all maps are exported."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,copy
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'inherited'/'projection159'/'code'))
from reduce_radical import norm,terms,add,scale,mul,V,subst,canonical,digest,metric

def dot(u,v): return sum(a*b for a,b in zip(u,v))
def gs(B):
    stars=[];mu=[];length=[]
    for row in B:
        v=list(map(F,row));ms=[]
        for u,l in zip(stars,length):
            a=dot(list(map(F,row)),u)/l;ms.append(a)
            v=[x-a*y for x,y in zip(v,u)]
        stars.append(v);mu.append(ms);length.append(dot(v,v))
    return mu,length
def lll(B):
    B=copy.deepcopy(B);r=len(B);T=[[int(i==j) for j in range(r)] for i in range(r)];k=1
    while k<r:
        for j in range(k-1,-1,-1):
            mu,_=gs(B);a=mu[k][j];q=(2*a.numerator+a.denominator)//(2*a.denominator)
            if q:
                B[k]=[u-q*v for u,v in zip(B[k],B[j])]
                T[k]=[u-q*v for u,v in zip(T[k],T[j])]
        mu,le=gs(B)
        if le[k]>=(F(3,4)-mu[k][k-1]**2)*le[k-1]: k+=1
        else:
            B[k],B[k-1]=B[k-1],B[k];T[k],T[k-1]=T[k-1],T[k];k=max(1,k-1)
    return B,T
def inv(A):
    n=len(A);M=[list(map(F,row))+[F(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
    for i in range(n):
        j=next(j for j in range(i,n) if M[j][i]);M[i],M[j]=M[j],M[i]
        c=M[i][i];M[i]=[x/c for x in M[i]]
        for j in range(n):
            if j!=i:
                c=M[j][i];M[j]=[a-c*b for a,b in zip(M[j],M[i])]
    if any(x.denominator!=1 for row in M for x in row[n:]):raise ValueError('nonintegral inverse')
    return [[int(x) for x in row[n:]] for row in M]

def run(inp,out):
    e=json.loads(Path(inp).read_text());n=len(e['variables']);
    if n!=220:raise ValueError('requires exact 220 parent')
    J=[9,10,20,21,34];a=[12,16,4,-1,1];constant=4;omit=6
    affine={():constant,**{(i,):v for i,v in zip(J,a)}}
    combo=[[-1,6],[1,19]]
    actual=add(*(scale(norm(e['residuals'][j]['terms']),c) for c,j in combo))
    if actual!=affine:raise ValueError('unexpected affine combination')
    B0=[[1,0,0,0,-12],[0,1,0,0,-16],[0,0,1,0,-4],[0,0,0,1,1]]
    B,T=lll(B0);Ti=inv(T);part=[0,0,-1,0,0]
    keep=[i for i in range(n) if i!=J[-1]];ren={k:j for j,k in enumerate(keep)}
    lift={i:V(ren[i]) for i in keep if i not in J}
    for j,i in enumerate(J):lift[i]=add({():part[j]} if part[j] else {},*[{(ren[J[k]],):B[k][j]} for k in range(4) if B[k][j]])
    reverse={ren[i]:V(i) for i in keep if i not in J}
    for k in range(4):reverse[ren[J[k]]]=add(*[scale(add(V(J[j]),{():-part[j]}),Ti[j][k]) for j in range(4)])
    if subst(affine,lift):raise ValueError('lift misses hyperplane')
    for j,p in reverse.items():
        if subst(p,lift)!=V(j):raise ValueError('inverse failure')
    rows=[]
    for j,row in enumerate(e['residuals']):
        if j!=omit:rows.append(dict(row,terms=terms(subst(norm(row['terms']),lift))))
    ee=copy.deepcopy(e);ee['variables']=[e['variables'][i].copy() for i in keep]
    for k in range(4):ee['variables'][ren[J[k]]]['name']='lattice_affine.'+str(k)
    ee['residuals']=rows;ee['variant']=e['variant']+':small_integral_affine_coordinates'
    cert={'schema':'integral_affine_hyperplane_v1','input_sha256':digest(e),'output_sha256':digest(ee),
        'input_dimension':n,'output_dimension':n-1,'affine_terms':terms(affine),'row_combination':combo,'omitted_row':omit,
        'active_old_indices':J,'particular_solution':part,'initial_basis':B0,'basis':B,'unimodular_transform':T,'inverse_transform':Ti,
        'lift_old_from_new':[terms(lift[i]) for i in range(n)],'project_new_from_old':[terms(reverse[i]) for i in range(n-1)]}
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    expanded=add(*(mul(norm(r['terms']),norm(r['terms'])) for r in rows))
    for name,o in [('equation.json',ee),('affine_lattice_certificate.json',cert),('metrics.json',metric(ee,True)),('expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':n-1,'terms':terms(expanded)})]:(out/name).write_bytes(canonical(o))
    print('basis',B,'T',T,'metrics',metric(ee,True))
if __name__=='__main__':run(sys.argv[1],sys.argv[2])
