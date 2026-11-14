import functools,itertools
@functools.lru_cache(maxsize=200000)
def prefix(atoms,n):
 if n==0:return ((),)
 if not atoms:return tuple(itertools.product((0,1),repeat=n))
 a,*rest=atoms;rest=tuple(rest)
 if a[0]=='blank':return ((0,)*n,)
 if a[0]!='run':return tuple(itertools.product((0,1),repeat=n))
 bit,coef=a[1:]; minimum=coef[0]; variable=any(coef[1:])
 if minimum>=n:return ((bit,)*n,)
 lengths=range(minimum,n+1) if variable else [minimum]
 return tuple(set((bit,)*k+p for k in lengths for p in prefix(rest,n-k)))
