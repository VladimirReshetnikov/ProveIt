#!/usr/bin/env python3
"""Independent static/finite-model checks. NOT Lean elaboration or theorem proofs.

Run with python or python -O. Uses only the standard library and writes generator
replay output in a temporary directory, never over the author's candidate files.
"""
import hashlib,itertools,json,pathlib,re,shutil,subprocess,sys,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
REL=pathlib.Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
SRC=ROOT/'sources'/REL;C=ROOT/'local_candidates'
TARGETS={'WangTiles942PhysicalOrder.lean':['strictMono_fin_eq_self'],
         'IterationSize.lean':['iterate_depth'],
         'SidonPositions.lean':['weight_injective','pairWeight_injective']}
MODEL_COUNTS={}

def require(condition,message):
    if not condition:raise ValueError(message)

def body_spans(text,names):
    spans=[]
    for name in names:
        starts=list(re.finditer(r'^theorem '+re.escape(name)+r'\b',text,re.M))
        require(len(starts)==1,'nonunique theorem '+name)
        start=starts[0].start()
        # Here every continuation of each selected declaration is indented;
        # its next column-zero line begins a comment or another declaration.
        first_end=text.find('\n',start)
        nxt=re.search(r'^\S',text[first_end+1:],re.M)
        end=first_end+1+nxt.start() if nxt else len(text)
        assign=text.find(':=',start,end)
        require(assign!=-1,'missing proof assignment '+name)
        spans.append((assign+2,end,name))
    return spans

def outside_proofs(text,names):
    for start,end,name in sorted(body_spans(text,names),reverse=True):
        text=text[:start]+' <PROOF '+name+'>\n\n'+text[end:]
    return text

def no_new_trust_tokens(old,new):
    # Deliberately conservative: tokens in comments/strings also trigger review.
    for token in ['sorry','admit','axiom']:
        pattern=r'\b'+token+r'\b'
        require(len(re.findall(pattern,new))<=len(re.findall(pattern,old)),
                'new trust token '+token)

def apply_patch(source,patch,name):
    lines=patch.splitlines(True);require(len(lines)>=3,'short patch')
    require(lines[0].rstrip('\n')=='--- a/'+str(REL/name),'wrong old path')
    require(lines[1].rstrip('\n')=='+++ b/'+str(REL/name),'wrong new path')
    original=source.splitlines(True);out=[];cursor=0;pos=2;hunks=0
    while pos<len(lines):
        h=re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?',lines[pos])
        require(h is not None,'bad hunk header')
        old_start,old_count,new_start,new_count=[int(h.group(i)) if h.group(i) is not None else 1 for i in range(1,5)]
        require(old_start-1>=cursor,'overlapping/backward hunk')
        out.extend(original[cursor:old_start-1]);cursor=old_start-1
        require(len(out)==new_start-1,'new line offset mismatch')
        seen_old=seen_new=0;pos+=1;hunks+=1
        while pos<len(lines) and not lines[pos].startswith('@@'):
            row=lines[pos];require(row[:1] in [' ','+','-'],'unsupported diff row')
            op,text=row[0],row[1:]
            if op in [' ','-']:
                require(cursor<len(original) and original[cursor]==text,'source/context mismatch')
                cursor+=1;seen_old+=1
            if op in [' ','+']:out.append(text);seen_new+=1
            pos+=1
        require((seen_old,seen_new)==(old_count,new_count),'hunk count mismatch')
    require(hunks>0,'no hunks');out.extend(original[cursor:]);return ''.join(out)

def strict_inc(f):return all(f[i]<f[j] for i in range(len(f)) for j in range(i+1,len(f)))
def monotone(f):return all(f[i]<=f[j] for i in range(len(f)) for j in range(i+1,len(f)))
def weight(m,i):return (2*m*m+1)*i+i*i

class ArtifactChecks(unittest.TestCase):
    def test_patches_reproduce_candidates(self):
        for name in TARGETS:
            with self.subTest(file=name):
                self.assertEqual(apply_patch((SRC/name).read_text(),(C/'patches'/(name+'.patch')).read_text(),name),(C/'candidate'/name).read_text())

    def test_only_intended_proof_bodies_changed(self):
        for name,names in TARGETS.items():
            with self.subTest(file=name):
                a=(SRC/name).read_text();b=(C/'candidate'/name).read_text()
                self.assertEqual(outside_proofs(a,names),outside_proofs(b,names))
                for n in names:
                    (s,e,_),=body_spans(a,[n]);(t,u,_),=body_spans(b,[n]);self.assertNotEqual(a[s:e],b[t:u])

    def test_no_new_trust_tokens(self):
        for name in TARGETS:no_new_trust_tokens((SRC/name).read_text(),(C/'candidate'/name).read_text())

    def test_hash_metrics_and_source_binding(self):
        manifest={e['path']:e for e in json.loads((ROOT/'provenance/source_manifest.json').read_text())['sources']}
        metrics=json.loads((C/'metrics.json').read_text());self.assertEqual({r['file'] for r in metrics},set(TARGETS))
        for r in metrics:
            a=(SRC/r['file']).read_bytes();b=(C/'candidate'/r['file']).read_bytes();entry=manifest[str(REL/r['file'])]
            self.assertEqual(hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest(),entry['sha'])
            self.assertEqual(hashlib.sha256(a).hexdigest(),entry['sha256'])
            self.assertEqual(hashlib.sha256(a).hexdigest(),r['source_sha256']);self.assertEqual(hashlib.sha256(b).hexdigest(),r['candidate_sha256'])
            self.assertEqual(len(a.splitlines()),r['source_lines']);self.assertEqual(len(b.splitlines()),r['candidate_lines'])
            self.assertEqual(len(a.splitlines())-len(b.splitlines()),r['net_lines_saved']);self.assertEqual(r['status'],'UNCOMPILED')

    def test_generator_isolated_replay(self):
        with tempfile.TemporaryDirectory(prefix='round5-candidate-replay-') as tmp:
            root=pathlib.Path(tmp);(root/'sources'/REL).mkdir(parents=True)
            for sub in ['candidate','patches']:(root/'local_candidates'/sub).mkdir(parents=True)
            for name in TARGETS:shutil.copyfile(SRC/name,root/'sources'/REL/name)
            builder=root/'local_candidates/build_candidates.py';shutil.copyfile(C/'build_candidates.py',builder)
            run=subprocess.run([sys.executable,str(builder)],capture_output=True,text=True)
            self.assertEqual(run.returncode,0,run.stderr)
            for name in TARGETS:
                for sub,file in [('candidate',name),('patches',name+'.patch')]:self.assertEqual((root/'local_candidates'/sub/file).read_bytes(),(C/sub/file).read_bytes())
            self.assertEqual((root/'local_candidates/metrics.json').read_bytes(),(C/'metrics.json').read_bytes())

    def test_guard_rejects_changed_signature(self):
        name='IterationSize.lean';a=(SRC/name).read_text();bad=(C/'candidate'/name).read_text().replace('theorem iterate_depth {f : ℕ → ℕ}','theorem iterate_depth {f : ℕ → ℤ}')
        self.assertNotEqual(outside_proofs(a,TARGETS[name]),outside_proofs(bad,TARGETS[name]))

    def test_guard_rejects_changed_definition(self):
        name='SidonPositions.lean';a=(SRC/name).read_text();bad=(C/'candidate'/name).read_text().replace('2 * m ^ 2 + 1','2 * m ^ 2 + 2',1)
        self.assertNotEqual(outside_proofs(a,TARGETS[name]),outside_proofs(bad,TARGETS[name]))

    def test_guard_rejects_new_trust_tokens(self):
        for token in ['sorry','admit','axiom']:
            with self.subTest(token=token):
                with self.assertRaises(ValueError):no_new_trust_tokens('theorem x : True := by trivial','theorem x : True := by '+token)

    def test_patch_guard_rejects_source_drift(self):
        name='IterationSize.lean';a=(SRC/name).read_text().replace('exact congrArg Expr.depth he','exact congrArg Expr.depth OTHER')
        with self.assertRaises(ValueError):apply_patch(a,(C/'patches'/(name+'.patch')).read_text(),name)

    def test_patch_guard_rejects_path_and_counts(self):
        name='IterationSize.lean';a=(SRC/name).read_text();patch=(C/'patches'/(name+'.patch')).read_text()
        with self.assertRaises(ValueError):apply_patch(a,patch.replace('+++ b/','+++ b/../',1),name)
        with self.assertRaises(ValueError):apply_patch(a,patch.replace('@@ -69,9','@@ -69,8',1),name)

class FiniteModels(unittest.TestCase):
    def test_all_strictly_increasing_selfmaps_n0_through6_are_identity(self):
        total=accepted=0
        for n in range(7):
            found=0
            for f in itertools.product(range(n),repeat=n):
                total+=1
                if strict_inc(f):
                    self.assertEqual(f,tuple(range(n)));found+=1;accepted+=1
            self.assertEqual(found,1,('n',n))
        MODEL_COUNTS.update(finite_selfmaps_examined=total,strictly_increasing_selfmaps=accepted,max_finite_ordinal=6)

    def test_order_model_hypothesis_controls(self):
        self.assertTrue(monotone((0,0)));self.assertFalse(strict_inc((0,0)));self.assertNotEqual((0,0),(0,1))
        self.assertEqual(len(set((1,0))),2);self.assertFalse(strict_inc((1,0)));self.assertNotEqual((1,0),(0,1))
        # A strictly increasing map into a larger ordinal need not fix points.
        self.assertTrue(strict_inc((1,2)));self.assertNotEqual((1,2),(0,1))

    def test_sidon_pair_sum_iff_exhaustive_small_indices(self):
        cases=0
        for m in range(7):
            for i,j,k,l in itertools.product(range(m+1),repeat=4):
                eq=weight(m,i)+weight(m,j)==weight(m,k)+weight(m,l)
                unordered=((i==k and j==l) or (i==l and j==k));self.assertEqual(eq,unordered);cases+=1
        MODEL_COUNTS['sidon_quadruples_examined']=cases

    def test_sidon_diagonal_injectivity_including_zero(self):
        cases=0
        for m in range(13):
            for i,j in itertools.product(range(m+1),repeat=2):
                self.assertEqual(weight(m,i)==weight(m,j),i==j)
                diagonal=((i==j and i==j) or (i==j and i==j))
                self.assertEqual(2*weight(m,i)==2*weight(m,j),diagonal);cases+=1
        MODEL_COUNTS['diagonal_pairs_examined']=cases

    def test_sorted_pair_and_swap_branch(self):
        cases=swap_cases=0
        for m in range(10):
            pairs=list(itertools.combinations_with_replacement(range(m+1),2))
            for p,q in itertools.product(pairs,repeat=2):
                self.assertEqual(sum(weight(m,x) for x in p)==sum(weight(m,x) for x in q),p==q);cases+=1
                if p[0]==q[1] and p[1]==q[0]:self.assertEqual(p,q);self.assertEqual(p[0],p[1]);swap_cases+=1
        MODEL_COUNTS.update(sorted_pair_comparisons=cases,sorted_swap_cases=swap_cases)

    def test_sidon_guard_controls(self):
        # Without canonical sorting, sums cannot distinguish an ordered swap.
        p,q=(0,1),(1,0);self.assertNotEqual(p,q);self.assertEqual(sum(weight(1,x) for x in p),sum(weight(1,x) for x in q));self.assertFalse(q[0]<=q[1])
        # Injective weights alone do not imply pair-sum injectivity.
        linear=lambda i:i;self.assertEqual(linear(0)+linear(2),linear(1)+linear(1));self.assertNotEqual((0,2),(1,1))
        # Non-strict monotonicity and a nonself codomain are separate guards.
        self.assertFalse(strict_inc((0,0)))

if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    summary={'kind':'static artifact checks and independent finite models; NOT Lean elaboration','tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'success':result.wasSuccessful(),'models':MODEL_COUNTS,'candidate_status':'UNCOMPILED','scope':'three local candidate files only, preserving definitions and all theorem signatures'}
    print(json.dumps(summary,indent=2));sys.exit(not result.wasSuccessful())
