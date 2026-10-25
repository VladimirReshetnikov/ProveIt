from pathlib import Path
import copy
import hashlib
import json
import sys
import tempfile

root=Path(__file__).resolve().parent/'round18_closure/signed'
sys.path.insert(0,str(root))
import check_spheres as check
import build_spheres as build
names=['sphere_grouped_centered_merged_odd','sphere_sparse_centered_merged_odd']
results={}
rejected=[]
for name in names:
    path=root/name
    results[name]=check.check(path)
    eq=json.loads((path/'equation.json').read_text())
    for label in ['sphere.interval_group.0','shared.frame_definition','radix.odd_square']:
        altered=copy.deepcopy(eq)
        row=next(r for r in altered['residuals'] if r['label']==label)
        row['terms'][0][0]+=1
        try:
            check.check(path,altered)
        except ValueError:
            rejected.append(name+':'+label)
        else:
            raise ValueError('Corruption not rejected')
controls=check.controls()
comparisons=[]
with tempfile.TemporaryDirectory() as td:
    build.ROOT=Path(td)
    for name in names:
        parent=name.replace('sphere_','strict_').replace('_merged_odd','')
        build.build(parent,merged=True,odd_square=True)
        fresh=Path(td)/name
        old=root/name
        if sorted(p.name for p in fresh.iterdir()) != sorted(p.name for p in old.iterdir()):
            raise ValueError('Old signed selected endpoint file set differs')
        for p in fresh.iterdir():
            if p.read_bytes() != (old/p.name).read_bytes():
                raise ValueError('Old signed reconstruction bytes differ: '+str(p))
            comparisons.append(name+'/'+p.name)
print(json.dumps({'status':'PASS','selected_old_signed':results,'negative_controls_rejected':rejected,
                  'arithmetic_controls':controls,'byte_identical_rebuilt_files':comparisons},indent=2))
