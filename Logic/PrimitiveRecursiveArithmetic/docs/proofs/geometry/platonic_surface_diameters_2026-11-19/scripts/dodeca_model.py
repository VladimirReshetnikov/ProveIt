"""Check the support planes, edges, and antipode labels of the 3D model."""
from itertools import product
from dodeca_upper import FACES, antipodes, kmul, ksub, nonneg
def plus(p,q):
    return (p[0]+q[0],p[1]+q[1])
def vecminus(p,q):
    return [ksub(a,b) for a,b in zip(p,q)]
def dot(p,q):
    w=(0,0)
    for a,b in zip(p,q):w=plus(w,kmul(a,b))
    return w
def cross(p,q):
    return [ksub(kmul(p[(i+1)%3],q[(i+2)%3]),kmul(p[(i+2)%3],q[(i+1)%3])) for i in range(3)]
def verify():
    vertices=[[(s,0) for s in signs] for signs in product((-1,1),repeat=3)]
    for i in range(3):
        for a,b in product((-1,1),repeat=2):
            w=[(0,0),(-a,a),(0,b)]
            vertices.append(w[-i:]+w[:-i])
    for face in FACES:
        p,q,r= [vertices[k] for k in face[:3]]
        n=cross(vecminus(q,p),vecminus(r,p))
        assert dot(n,p)==(2,0)
        slack=[ksub((2,0),dot(n,u)) for u in vertices]
        assert all(nonneg(s) for s in slack)
        assert set(face)=={j for j in range(20) if slack[j]==(0,0)}
        for i,k in enumerate(face):
            e=vecminus(vertices[k],vertices[face[i-1]])
            assert dot(e,e)==(8,-4)
    for i,j in antipodes().items():
        assert all(plus(a,b)==(0,0) for a,b in zip(vertices[i],vertices[j]))
if __name__=='__main__':
    verify()
    print('Dodecahedron: 12 oriented support planes, unit edges after scaling, and antipodes verified.')
