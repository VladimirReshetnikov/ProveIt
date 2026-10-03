#!/usr/bin/env python3
"""Portable pinned replay and bounded independent audit of four surreal archives."""
if not __debug__:raise RuntimeError('Run without optimized Python')
import argparse,difflib,hashlib,io,json,re,stat,subprocess,sys,tempfile,types,zipfile
from collections import Counter
from fractions import Fraction
from itertools import permutations,product
from pathlib import Path,PurePosixPath
PINNED_COMMIT='4e270aa4648c5fd7e18626507531046715976535'
PATCH_SHA='a2f6d15df6d60bb4732434040f403e5cf3e9bc437b56582184742d3dd1e1046e'
PATCHED_SOURCE_SHA='07c432933395870722d71a3ceb788c7f0d3454e44f3a31c7e4f3e6b448ef7bd7'
OLD_TEXT="For non-set-like relations, the model's class collection can matter to\nthe well-order assertion."
NEW_TEXT='Over $\\GBC$, well-foundedness of any fixed class relation is equivalent\nto the absence of a set-coded descending $\\omega$-sequence. Keeping the\nsets and the relation fixed while enlarging the class collection therefore\ndoes not change its internal well-foundedness. What may change is which\nclass relations are available; internal and external well-foundedness\nmust also be distinguished.'
INVENTORY=[{'archive': 'Surreal_Well_Orders_Research.zip',
  'label': 'research',
  'members': [{'path': 'surreal_well_orders/README.md',
               'sha256': '7d2a38c8a48685083851ae2e07a39d50a2f0011f5f10a7a13be8cd9983c29ba3',
               'size': 3750},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': 'b583206a78a401a6d40eec3fe2d14a1a4a1232c258cfd9322b6157154180696e',
               'size': 5239},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '66a3c25862ed389c8c46b254da14aa81220213c570844d829036108a463e5b8a',
               'size': 570},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'e368b543d32d374c4e672c945bb3d3f0b0c739f3e8961477f62a5f31c0217105',
               'size': 334883},
              {'path': 'surreal_well_orders/article.tex',
               'sha256': 'bd87c866b520a5261178b28e23fb6df3bcbf2c431bd8414b46f919b022ffc56c',
               'size': 80261},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '3894153b599649376c75971722a7a377ab84b1b34280e80a955dad8b91453a66',
               'size': 221},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '508bf3668241708b72043bff16bb64b559842b745572a2a6f05e4be65a8d2f64',
               'size': 10211},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': '29c3beb5bed2dce88b2a70fa0a55408ce5510b95016b7a93ce705edf28ea9460',
               'size': 576}],
  'sha256': '8aebf0ab80207a4e2165be6f7a329eff18b90134128b02e65c4732c97c252ee9'},
 {'archive': 'Surreal_Well_Orders_Research (1).zip',
  'label': 'research1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': 'd99f4a6c05f37c3a4c61118ceb05d2246f5d6dd2fbccf1fc07a575f665cfc256',
               'size': 352071},
              {'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': '2a3f5c055d64adc4f3954b1c0224e52c710f57873617d3f756c207ed26a4d4a0',
               'size': 95748},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '5f63b9ee2fead063c4a9c23523996d699284acb1e12df8783790483033194eee',
               'size': 3966},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '081a9006286946109415a3b6b04bef6a3087df4c2c8ae015c0f4364725c22ce6',
               'size': 428},
              {'path': 'surreal_well_orders/verify_finite.py',
               'sha256': '2e429bc5a52702a922f44ee60b7e1a91dc9ef9924bc7c8649bfbae2069e843d5',
               'size': 3721},
              {'path': 'surreal_well_orders/verification_results.json',
               'sha256': '6d9bc26ba180fed1832106e605ab3c537b65be7ac481916d301050ddf076cf60',
               'size': 332},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': '8fa626f69eb33d7cf8e396cbc2a2a2e02db11170cc7f69d75cfac9172cea600a',
               'size': 506}],
  'sha256': '36c7f6ac22cd2a665aa078eb99eeffef170cb2d6c0cadab31417562f147d8179'},
 {'archive': 'surreal_well_orders.zip',
  'label': 'lower',
  'members': [{'path': 'surreal_well_orders/article.tex',
               'sha256': '44ce2e2de4bdf15373709b6c120be7e03eadd3d868149152fefb409ae0dcd450',
               'size': 79635},
              {'path': 'surreal_well_orders/article.pdf',
               'sha256': 'fee434ab4074dc736846e7322abba97e0c12ad2f3b4f72df39f2a98b606004a4',
               'size': 484264},
              {'path': 'surreal_well_orders/README.md',
               'sha256': '48ec3a58af77dcb314dcb2be5a517a1e405a12ef7e0bc0122d25190b3b93e78a',
               'size': 4326},
              {'path': 'surreal_well_orders/RESEARCH_STATUS.md',
               'sha256': '9536ab4b79e344bd2f6e5c80ffc9e16e0ac1e5bc6f7b289372d04b7d97b74904',
               'size': 8647},
              {'path': 'surreal_well_orders/build.sh',
               'sha256': '23e41596cf1fbe0d3d18c48b831c18915bf63b834183d570ae7aef456ba36c68',
               'size': 402},
              {'path': 'surreal_well_orders/code/finite_checks.py',
               'sha256': '2bacfce134b39479d910159486079aa5792550a1fe7e57c54b79d9605827f7a3',
               'size': 7326},
              {'path': 'surreal_well_orders/data/finite_checks.json',
               'sha256': 'b541630a53904c56aa8fbf2f2e6bb9a1b731735e58473608b44f4e90546e521c',
               'size': 845},
              {'path': 'surreal_well_orders/SHA256SUMS.txt',
               'sha256': 'a1118dc2384a9ccf0acf27d43972a9f257b158e24e1ea3aeb105a3f13963a4ba',
               'size': 570}],
  'sha256': '1edf59eaa0febdc0b7c9da581d9a6a65cc2ae88b99c166756ffd58f8aa4d4d5d'},
 {'archive': 'surreal_well_orders (1).zip',
  'label': 'lower1',
  'members': [{'path': 'surreal_well_orders/surreal_well_orders.tex',
               'sha256': 'b08eaac10e7cd7573713490422d6d3a590cdac8df890743b98c07c3f5742dac2',
               'size': 126780},
              {'path': 'surreal_well_orders/surreal_well_orders.pdf',
               'sha256': '7dbce2ecb7cd661514465887ff5ab68603ff0c7a46dc9c7f407744a67c513552',
               'size': 543575},
              {'path': 'surreal_well_orders/README.txt',
               'sha256': 'f0b5a8dd762e56fbf58b4bdeeea3eb5be1904926a396c1d2206a9d0ea21e8fd7',
               'size': 2414},
              {'path': 'surreal_well_orders/repository_audit.md',
               'sha256': '9332fff9474586f329927f9fc44c53ba53caf689ed3aee561fa44b4935130f39',
               'size': 10682},
              {'path': 'surreal_well_orders/finite_checks.py',
               'sha256': '751e173bf3529e93d86a0281e1385515ec8220a1b97ca682a2ecef8bd895b844',
               'size': 6538},
              {'path': 'surreal_well_orders/finite_checks_results.txt',
               'sha256': '997710f1aef157365105381378e0d4638f67092c847d3df8a93befbf561f52af',
               'size': 939}],
  'sha256': 'e48ab1b54681787324fd01953ba093d2b7abe546673ccd0f0a0bcb59e232e33a'}]

def need(x,msg):
    if not x:raise ValueError(msg)
def exact(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
    if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def sha(data):return hashlib.sha256(data).hexdigest()
def archive_data(repo,name):
    p=Path(repo)/'docs/incoming'/name
    if p.exists():return p.read_bytes()
    r=subprocess.run(['git','show',PINNED_COMMIT+':docs/incoming/'+name],cwd=repo,capture_output=True,timeout=60)
    need(r.returncode==0,'Missing archive at both current path and pinned Git object '+name);return r.stdout

def extract(data,directory,entry):
    need(sha(data)==entry['sha256'],'Archive pin '+entry['archive']);expected={m['path']:m for m in entry['members']}
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        seen=set()
        for info in z.infolist():
            p=PurePosixPath(info.filename)
            need(not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename and ':' not in info.filename,'Unsafe archive path')
            need(info.filename not in seen and not stat.S_ISLNK(info.external_attr>>16),'Duplicate or symlink archive member');seen.add(info.filename)
            need(not info.is_dir() and info.filename in expected,'Unexpected archive member')
            need(info.file_size<2000000,'Bounded member size');raw=z.read(info);m=expected[info.filename]
            need(len(raw)==m['size'] and sha(raw)==m['sha256'],'Full member authentication')
            out=directory.joinpath(*p.parts);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
        need(seen==set(expected),'Exact archive inventory')
    return directory/'surreal_well_orders'

def load(path,name):
    module=types.ModuleType(name);module.__file__=str(path);sys.modules[name]=module
    exec(compile(path.read_bytes(),str(path),'exec'),module.__dict__);return module

def sign_value(s):
    """Independent rational value of a finite surreal sign expansion."""
    if not s:return Fraction(0)
    run=next((i for i,v in enumerate(s) if v!=s[0]),len(s))
    value=Fraction(run*s[0])
    for i in range(run,len(s)):value+=Fraction(s[i],2**(i-run+1))
    return value

def independent(roots):
    A=load(roots['research']/'code/finite_checks.py','_surreal_review_A')
    B=load(roots['research1']/'verify_finite.py','_surreal_review_B')
    C=load(roots['lower']/'code/finite_checks.py','_surreal_review_C')
    D=load(roots['lower1']/'finite_checks.py','_surreal_review_D')
    counts=Counter();sgn=lambda x:(x>0)-(x<0)
    words=[s for n in range(5) for s in product((-1,1),repeat=n)]
    for s,t in product(words,repeat=2):
        actual=sgn(sign_value(s)-sign_value(t))
        need(B.surreal_compare(s,t)==C.sign_compare(s,t)==D.compare_signs(s,t)==actual,'Independent dyadic sign order')
        need(sgn((B.code(s)>B.code(t))-(B.code(s)<B.code(t)))==actual,'Binary terminated source code')
        need(B.code(s)==C.code(s),'Matching two binary code variants')
        need(sgn(sign_value(D.sign_code(s))-sign_value(D.sign_code(t)))==actual,'Signed source code arithmetic order')
        counts['finite_sign_pairs_against_dyadic_arithmetic']+=1
    small=[s for n in range(3) for s in product((-1,1),repeat=n)]
    allwords=[w for n in range(3) for w in product(small,repeat=n)]
    values={w:sign_value(D.word_code(w)) for w in allwords}
    for u,v in product(allwords,repeat=2):
        a=tuple(sign_value(s) for s in u);b=tuple(sign_value(s) for s in v)
        need(sgn((a>b)-(a<b))==sgn(values[u]-values[v]),'Full repeated-entry word code arithmetic order')
        counts['finite_word_pairs_against_dyadic_arithmetic']+=1
    need(values[()]==0 and all(v>0 for w,v in values.items() if w),'Empty and positive word images')
    # Two independent predecessor formulas versus a direct permutation-list oracle.
    ps=list(permutations(range(5)))
    masks={p:D.predecessor_masks(p) for p in ps}
    for u,v in product(ps,repeat=2):
        prefix=tuple(a for a,b in zip(u,v)) if u==v else u[:next(i for i in range(5) if u[i]!=v[i])]
        need(C.common_prefix_formula(u,v)==frozenset(prefix),'Class-prefix formula finite shadow')
        need(D.compare_by_predecessors(u,v,masks[u],masks[v])==sgn((u>v)-(u<v)),'Predecessor-disagreement comparison')
        counts['two_raw_prefix_formulas']+=1
    # Check the actual fresh-separator algorithm on all separated lower/upper
    # selections of the six three-letter permutations, retaining an unused tail.
    pool=[p+(3,) for p in permutations(range(3))]
    for labels in product(range(3),repeat=len(pool)):
        left=[p for p,c in zip(pool,labels) if c==1];right=[p for p,c in zip(pool,labels) if c==2]
        if any(not u<v for u in left for v in right):continue
        result=A.forced_separator(left,right);need(len(set(result))==len(result),'Injective finite stopping prefix')
        for p in left:
            k=next(i for i,(x,y) in enumerate(zip(p,result)) if x!=y);need(p[k]<result[k],'Permanent lower first difference')
        for p in right:
            k=next(i for i,(x,y) in enumerate(zip(p,result)) if x!=y);need(result[k]<p[k],'Permanent upper first difference')
        counts['exhaustive_separated_finite_family_patterns']+=1
    # An independent finite row schedule with reversed baselines verifies that
    # the result is not tied to sorted row enumerations in the source fixture.
    for rows in range(1,4):
        for width in range(1,4):
            schedule=C.schedule(rows,width)
            need(sorted(schedule)==list(product(range(rows),range(width))),'Schedule bijection')
            def encode(v):
                rr=[]
                for i,x in enumerate(v):
                    row=list(reversed(range(i*width,(i+1)*width)));k=row.index(i*width+x);row[0],row[k]=row[k],row[0];rr.append(row)
                return tuple(rr[i][j] for i,j in schedule)
            inputs=list(product(range(width),repeat=rows));images={v:encode(v) for v in inputs}
            for a,b in product(inputs,repeat=2):
                need((a<b)==(images[a]<images[b]),'First-varying-row scheduler with nonsorted baselines');counts['scheduler_pairs_reversed_baselines']+=1
    # Necessary boundaries, not counterexamples to the corrected theorems.
    relation_a=(0,1,2);relation_b=(0,2,1)
    def table(p):return tuple(int(p.index(a)<p.index(b)) for a in range(3) for b in range(3))
    need(relation_a<relation_b and table(relation_a)>table(relation_b),'Relation-table lex differs from enumeration lex')
    # Removing a terminator makes empty and repeated empty entry words collide.
    naive=lambda w:tuple(q for s in w for q in s)
    need(naive(())==naive(((),)) and D.word_code(())!=D.word_code(((),)),'Paid delimiter necessity')
    # A valid bijective schedule can reverse the first varying input row.
    need((0,1)<(1,0) and (1,0)>(0,1),'Arbitrary coordinate reordering is not lex invariant')
    return dict(counts=dict(counts),boundaries=dict(relation_table_example=[list(relation_a),list(relation_b)],delimiter_collision=[[],[[]]],arbitrary_row_reordering='Reversing two row coordinates reverses (0,1)<(1,0).'),
       scope='Finite regression checks only. Dyadic arithmetic independently interprets finite sign codes; no class recursion, singular-cardinal theorem, transfinite cut, or global-choice equivalence is established by these checks.')

def run(repo,patch=None):
    roots={};authors=[];manifest_checks=[];formal=[];originals={}
    with tempfile.TemporaryDirectory(prefix='batch80-surreal-replay-') as directory:
        directory=Path(directory)
        for entry in INVENTORY:
            label=entry['label'];data=archive_data(repo,entry['archive']);originals[label]=sha(data);root=extract(data,directory/label,entry);roots[label]=root
            m=root/'SHA256SUMS.txt';n=0
            if m.exists():
                for line in m.read_text().splitlines():
                    if not line.strip():continue
                    h,name=line.split(maxsplit=1);name=name.strip().lstrip('*');need(name in {str(PurePosixPath(x['path']).relative_to('surreal_well_orders')) for x in entry['members']},'Manifest path in authenticated archive')
                    need(sha((root/name).read_bytes())==h,'Author member manifest');n+=1
            manifest_checks.append(dict(label=label,verified_entries=n))
            tex=next(root.glob('*.tex'));text=tex.read_text()
            formal.append(dict(label=label,source=tex.name,lines=len(text.splitlines()),proof_blocks=len(re.findall(r'\\begin\{proof\}',text)),statements={kind:len(re.findall(r'\\begin\{'+kind+r'\}',text)) for kind in ('theorem','lemma','proposition','corollary')},section_outline=[dict(line=i,text=l.strip()) for i,l in enumerate(text.splitlines(),1) if l.startswith('\\section{')]))
        configs=[('research','code/finite_checks.py',['--output',str(directory/'research-fresh.json')],'data/finite_checks.json'),('research1','verify_finite.py',[],'verification_results.json'),('lower','code/finite_checks.py',['--output',str(directory/'lower-fresh.json')],'data/finite_checks.json'),('lower1','finite_checks.py',[],'finite_checks_results.txt')]
        for label,script,args,saved in configs:
            root=roots[label];before=(root/saved).read_bytes();r=subprocess.run([sys.executable,script,*args],cwd=root,capture_output=True,text=True,timeout=240)
            need(r.returncode==0,'Author replay '+label+': '+r.stderr)
            if label!='lower1':need(exact(json.loads(r.stdout),json.loads(before)),'Exact typed original author receipt '+label);report=json.loads(r.stdout)
            else:need(r.stdout==before.decode(),'Exact original text receipt');report=r.stdout
            authors.append(dict(label=label,command=['python3',script]+(['--output','PRIVATE_OUTPUT.json'] if args else []),exit_code=r.returncode,full_saved_output_matches=True,stdout_sha256=sha(r.stdout.encode()),report=report))
        regressions=independent(roots)
        # The sole repair is prose; source code and theorem hypotheses remain fixed.
        root=roots['research1'];old=(root/'surreal_well_orders.tex').read_text();need(old.count(OLD_TEXT)==1,'Unique imprecise sentence');new=old.replace(OLD_TEXT,NEW_TEXT)
        expected=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/surreal_well_orders.tex',tofile='b/surreal_well_orders.tex'))
        need(sha(expected.encode())==PATCH_SHA and sha(new.encode())==PATCHED_SOURCE_SHA,'Exact prose repair')
        patchbytes=expected.encode() if patch is None else Path(patch).read_bytes();need(sha(patchbytes)==PATCH_SHA,'Supplied patch pin');patchfile=directory/'repair.patch';patchfile.write_bytes(patchbytes)
        for extra in (['--dry-run'],[]):
            r=subprocess.run(['patch','--batch','--fuzz=0','-p1',*extra,'-i',str(patchfile)],cwd=root,capture_output=True,text=True,timeout=60);need(r.returncode==0,'Exact private prose patch apply: '+r.stdout+r.stderr)
        need(sha((root/'surreal_well_orders.tex').read_bytes())==PATCHED_SOURCE_SHA,'Patched source bytes')
        for entry in INVENTORY:need(sha(archive_data(repo,entry['archive']))==originals[entry['label']],'Original archive changed')
    return dict(status='PASS_WITH_ONE_SCOPED_EDITORIAL_CORRECTION',pinned_commit=PINNED_COMMIT,archives=INVENTORY,all_member_count=sum(len(e['members']) for e in INVENTORY),all_distinct_member_hashes=len({m['sha256'] for e in INVENTORY for m in e['members']}),author_manifests=manifest_checks,formal_source_census=formal,author_replays=authors,independent_finite_checks=regressions,
      editorial_repair=dict(label='research1',source='surreal_well_orders.tex',original_lines=[762,766],patch_sha256=PATCH_SHA,patched_source_sha256=PATCHED_SOURCE_SHA,finding='In GBC, fixed-relation internal well-foundedness is determined by set-coded descending omega sequences; it does not change merely by changing the classes over the same sets. Availability of relations and external well-foundedness are separate.'),
      primary_checks=[dict(url='https://arxiv.org/html/1806.11180v1',sections='2–3, Theorem6',scope='Class-valued ETR versus set-valued recursion; GBC well-foundedness characterization; ETR suffices for abstract class-order comparability.'),dict(url='https://arxiv.org/html/math/0311165v1',sections='1',scope='Kanovei–Shelah index uses maps whose ranges are ultrafilters, not exhaustive well-orders of all reals or surreals.')],
      proof_review_scope='Written mathematical proof review and four finite script replays. No new Lean proof, TeX/PDF rebuild, priority claim, general effective simulation, paid fixed-scalar Diophantine compiler, or operation-count improvement. The scripts cannot establish any transfinite theorem.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',required=True,type=Path);p.add_argument('--patch',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();result=run(a.repo,a.patch)
    if a.expect:need(exact(result,json.loads(a.expect.read_text())),'Exact saved review receipt')
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],members=result['all_member_count'],author_outputs=[dict(label=r['label'],sha256=r['stdout_sha256']) for r in result['author_replays']],independent=result['independent_finite_checks'],repair=result['editorial_repair']),sort_keys=True,indent=2))
