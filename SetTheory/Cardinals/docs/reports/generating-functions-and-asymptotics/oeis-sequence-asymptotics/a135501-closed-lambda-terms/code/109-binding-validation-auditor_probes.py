#!/usr/bin/env python3
"""Independent materialized-tree finite audit. Run from any working directory.
Uses explicit guards under normal Python and -O; not an asymptotic proof.
"""
from functools import cache
from fractions import Fraction
from math import comb, factorial, prod
from pathlib import Path
import importlib.util,json,hashlib,sys
p=Path(__file__).resolve().parent.parent/'check.py'
spec=importlib.util.spec_from_file_location('target',p); c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
counts={}
height_records={(r['u'],r['b']):r['counts_by_height'] for r in json.loads((p.parent/'data'/'check_results.json').read_text())['height_records']}
def must(ok,label):
    counts[label]=counts.get(label,0)+1
    if not ok: raise RuntimeError(label)

# Materialized de Bruijn ASTs, rather than integer counting recurrence.
@cache
def terms(m,u,b):
    if not u and not b: return frozenset(('v',i) for i in range(m))
    out=set()
    if u:
        out.update(('l',x) for x in terms(m+1,u-1,b))
    if b:
        for ul in range(u+1):
            for bl in range(b):
                out.update(('a',x,y) for x in terms(m,ul,bl) for y in terms(m,u-ul,b-1-bl))
    return frozenset(out)
def measures(t):
    if t[0]=='v': return (0,0,0)
    if t[0]=='l':
        u,b,h=measures(t[1]);return u+1,b,h+1
    ul,bl,hl=measures(t[1]);ur,br,hr=measures(t[2]);return ul+ur,1+bl+br,max(hl,hr)
for u in range(1,7):
    for b in range(7-u):
        tt=terms(0,u,b)
        must(len(tt)==c.direct(0,u,b),'materialized_direct')
        must(all(measures(t)[:2]==(u,b) for t in tt),'AST_size')
        if (u,b) in height_records:
            hist=[0]*(u+1)
            for t in tt:hist[measures(t)[2]]+=1
            must(hist==height_records[u,b],'materialized_height_distribution')
for s in (0,1):
    A,D=c.total_and_moment(7,s)
    for n in range(8):
        # Derive admissibility from actual counted node sizes, without using c.admissible.
        allterms=set()
        for u in range(1,n+1):
            for b in range(n+1):
                if u+b+s*(b+1)==n: allterms.update(terms(0,u,b))
        must(len(allterms)==A[n],'materialized_model_total')
        must(sum(measures(t)[0] for t in allterms)==D[n],'materialized_model_moment')

# Independently instantiate the lower-bound injection from the proof.
for b in range(5):
    trees=c.binary_trees(b)
    must(len(trees)==comb(2*b,b)//(b+1),'Catalan_tree_inventory')
    must(len(set(trees))==len(trees),'distinct_binary_trees')
    for tree in trees:
        paths,v=c.leaf_paths(tree)
        must(len(paths)==b+1 and v==2*b+1,'leaf_slot_count')
        for u in range(1,7):
            for h in range(2,u+1):
                q=u-h+1
                if q>b+1:continue
                alpha=[0]*v;alpha[0]=h-1
                for leaf in paths[:q]:alpha[leaf[-1]]+=1
                depths=[sum(alpha[j] for j in path) for path in paths]
                must(sum(alpha)==u and max(depths)==h and min(depths)>=h-1,'height_injection')
                must(prod(depths)>=(h-1)**(b+1),'height_injection_weight')

# Materialize reduced trees; compare direct shape weights and each exact deficit product.
@cache
def reduced(k):
    if k==1:return (('u',None),)
    result=[('u',t) for t in reduced(k-1)]
    for j in range(1,k):
        result.extend(('b',a,b) for a in reduced(j) for b in reduced(k-j))
    return tuple(result)
def tree_data(t,m,u):
    if t is None:return 0,[],Fraction(1)
    if t[0]=='u':
        q,d,f=tree_data(t[1],m+1,u)
        return q,[u-m]+d,Fraction(u,u-m)*f
    q1,d1,f1=tree_data(t[1],m,u);q2,d2,f2=tree_data(t[2],m,u)
    return q1+q2+1,[u-m]+d1+d2,Fraction(u,u-m)*f1*f2
for u in range(1,10):
    weighted=Fraction(0);mx=Fraction(0)
    for t in reduced(u):
        q,ds,f=tree_data(t,0,u)
        weighted+=Fraction(1,2**q);mx=max(mx,f)
        must(all(sum(d<=j for d in ds)<=2*j-1 for j in range(1,u+1)),'individual_deficit_majorization')
        must(f<=Fraction(u**(2*u-1),factorial(u)**2),'individual_deficit_product')
    direct=sum(Fraction(comb(2*q,q),q+1)*comb(u+q-1,2*q)/2**q for q in range(u))
    must(weighted==direct,'materialized_weighted_shapes')
    @cache
    def maxf(m,k):
        if k==0:return Fraction(1)
        return Fraction(u,u-m)*max([maxf(m+1,k-1)]+[maxf(m,j)*maxf(m,k-j) for j in range(1,k)])
    must(mx==maxf(0,u),'materialized_max_deficit')

# Manifest parser and inventory checks run in a tiny disposable package.
# This tests schema strictness, not authenticity of a user-editable manifest.
import subprocess, tempfile, shutil
math_guards=sum(counts.values())
integrity=p.parent/'integrity.py'
with tempfile.TemporaryDirectory(prefix='report109-audit-inventory-') as temporary:
    root=Path(temporary)
    shutil.copyfile(integrity,root/'integrity.py')
    (root/'marker.txt').write_bytes(b'')
    records={name:{'sha256':hashlib.sha256((root/name).read_bytes()).hexdigest(),
                   'size_bytes':len((root/name).read_bytes())} for name in ('integrity.py','marker.txt')}
    baseline={'schema':1,'files':records}
    canonical=json.dumps(baseline,sort_keys=True)
    command=[sys.executable]+(['-O'] if sys.flags.optimize else [])+[str(root/'integrity.py')]
    (root/'manifest.json').write_text(canonical)
    result=subprocess.run(command,capture_output=True,text=True,timeout=30)
    must(result.returncode==0,'inventory_baseline')
    variants=[
        ('duplicate_key',canonical.replace('"schema": 1','"schema": 1, "schema": 1'),'duplicate JSON key'),
        ('boolean_schema',canonical.replace('"schema": 1','"schema": true'),'invalid manifest schema'),
        ('boolean_size',canonical.replace('"size_bytes": 0','"size_bytes": false'),'invalid size'),
        ('unsafe_path',canonical.replace('"marker.txt"','"../marker.txt"'),'unsafe manifest path'),
        ('invalid_hash',canonical.replace(records['marker.txt']['sha256'],'bad'),'invalid hash'),
    ]
    for name,manifest,diagnostic in variants:
        (root/'manifest.json').write_text(manifest)
        result=subprocess.run(command,capture_output=True,text=True,timeout=30)
        must(result.returncode!=0 and 'RuntimeError: '+diagnostic in result.stderr,'inventory_'+name)
    (root/'manifest.json').write_text(canonical)
    for name in ('nested/build/extra.txt','nested/qa/extra.txt','extra.txt'):
        extra=root/name;extra.parent.mkdir(parents=True,exist_ok=True);extra.write_text('unexpected')
        result=subprocess.run(command,capture_output=True,text=True,timeout=30)
        must(result.returncode!=0 and 'RuntimeError: inventory mismatch:' in result.stderr,'inventory_extra_file')
        extra.unlink()
    marker=root/'marker.txt'
    marker.unlink()
    result=subprocess.run(command,capture_output=True,text=True,timeout=30)
    must(result.returncode!=0 and 'RuntimeError: inventory mismatch:' in result.stderr,'inventory_missing_file')
    marker.symlink_to(root/'integrity.py')
    result=subprocess.run(command,capture_output=True,text=True,timeout=30)
    must(result.returncode!=0 and 'RuntimeError: symlink forbidden:' in result.stderr,'inventory_symlink')
    marker.unlink();marker.write_bytes(b'changed')
    result=subprocess.run(command,capture_output=True,text=True,timeout=30)
    must(result.returncode!=0 and 'RuntimeError: integrity mismatch:' in result.stderr,'inventory_changed_file')
print(json.dumps({'status':'PASS','checker_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                  'integrity_sha256':hashlib.sha256(integrity.read_bytes()).hexdigest(),
                  'optimization':sys.flags.optimize,'checks':counts,
                  'mathematical_guards':math_guards,'inventory_guards':sum(counts.values())-math_guards,
                  'total':sum(counts.values())},sort_keys=True))
