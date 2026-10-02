"""Pinned complete conservative-signal report replay and independent finite audit.

Default comparison is read-only except for isolated temporary author outputs.
The trillion-term expansion is never requested. Original ten CLI commands and
only the affected patched CLI run; patch changes the generic packet API only.
"""
if not __debug__:raise RuntimeError('Review requires enabled assertions')
import argparse
from collections import Counter,deque
from contextlib import contextmanager,ExitStack
from copy import deepcopy
import gzip
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE='Conservative_Signal_Diophantine_Frontend.zip'
ARRIVAL='2a8a3959980457aeb0fcf62e26860c809b5a2f42'
ARCHIVE_SHA='43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73'
SOURCE_SHA='94fb0aa513fc4c07860e2edab98bbb9d75fe713ed724f94e437e297a09a8666e'
PATCH_SHA='c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033'
REPAIRED_SHA='96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef'

def require(v,message):
    if not v:raise ValueError(message)

def sha(v):return hashlib.sha256(v).hexdigest()

@contextmanager
def load(path,name):
    sentinel=object();prior=sys.modules.get(name,sentinel)
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m
    try:
        spec.loader.exec_module(m);yield m
    finally:
        if prior is sentinel:sys.modules.pop(name,None)
        else:sys.modules[name]=prior

def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def verify(repo,patch):
    path=repo/'docs/incoming'/ARCHIVE
    data=path.read_bytes() if path.is_file() else subprocess.check_output(['git','show',f'{ARRIVAL}:docs/incoming/{ARCHIVE}'],cwd=repo)
    require(sha(data)==ARCHIVE_SHA and sha(patch.read_bytes())==PATCH_SHA,'Pinned archive or patch changed')
    counts=Counter()
    with ExitStack() as imports, tempfile.TemporaryDirectory(prefix='conservative-signal-review-') as td:
        td=Path(td);p=td/ARCHIVE;p.write_bytes(data)
        with zipfile.ZipFile(p) as z:
            names=z.namelist();require(len(names)==len(set(names)),'Duplicate members')
            require(all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names),'Unsafe member')
            members={n:sha(z.read(n)) for n in names if not n.endswith('/')}
            z.extractall(td)
        root=td/'conservative-signal-release';src=root/'code/quadratic_packet.py'
        require(sha(src.read_bytes())==SOURCE_SHA,'Original source changed')
        saved={str(p.relative_to(root)):json.loads(p.read_text()) for p in root.rglob('*.json')}
        done=subprocess.run(['sh','run-replay.sh'],cwd=root,capture_output=True,text=True,timeout=900)
        require(done.returncode==0,'Author replay failed: '+done.stdout[-2000:]+done.stderr[-2000:])
        require(done.stdout.rstrip().endswith('All exact replay suites passed.'),'Author replay did not finish')
        for name,value in saved.items():require(exact(json.loads((root/name).read_text()),value),'Author JSON changed: '+name)
        counts['original_author_cli_commands_passed']=10
        counts['archived_JSON_files_preserved']=len(saved)
        independent_path=Path(__file__).resolve().with_name('review_conservative_signal_independent.py')
        require(sha(independent_path.read_bytes())=='9f88d11c283b9443b09834244f3a73d02f96ade7e89b510d3da72c9358e08e53','Independent checker changed')
        independent=imports.enter_context(load(independent_path,'_signal_second_reader')).verify(root,patch)
        # Check the temporary import helper restores an exact caller-owned module.
        sentinel=object();prior=sys.modules.get('_signal_namespace_fixture',sentinel);stub=object()
        sys.modules['_signal_namespace_fixture']=stub
        try:
            with load(src,'_signal_namespace_fixture') as fixture:require(fixture is not stub,'Import did not replace stub')
            require(sys.modules['_signal_namespace_fixture'] is stub,'Caller module was not restored')
        finally:
            if prior is sentinel:sys.modules.pop('_signal_namespace_fixture',None)
            else:sys.modules['_signal_namespace_fixture']=prior
        counts['cold_exact_module_restore']=1
        old=imports.enter_context(load(src,'_signal_packet_original'))
        branch=(old.Branch(((1,),),()),);w=old.canonical_witness(branch,(1,),(1,))
        require(old.polynomial_value(branch,(1,),(1,999),w)==0,'Padded output defect changed')
        require(old.polynomial_value(branch,(1.0,),(1,),w)==0,'Float input defect changed')
        require(old.polynomial_value(branch,(1,),(1,),(w[0],w[1],((None,),)))==0,'Surplus slack defect changed')
        counts['original_false_validation_regressions']=3
        done=subprocess.run(['git','apply','--check',str(patch)],cwd=root,capture_output=True,text=True);require(done.returncode==0,done.stderr)
        done=subprocess.run(['git','apply',str(patch)],cwd=root,capture_output=True,text=True);require(done.returncode==0,done.stderr)
        require(sha(src.read_bytes())==REPAIRED_SHA,'Repair output changed')
        done=subprocess.run([sys.executable,'code/quadratic_packet.py'],cwd=root,capture_output=True,text=True,timeout=120);require(done.returncode==0,done.stderr)
        require(exact(json.loads((root/'receipts/QUADRATIC_PACKET_RESULTS.json').read_text()),saved['receipts/QUADRATIC_PACKET_RESULTS.json']),'Patched valid receipt changed')
        counts['affected_patched_cli_commands_passed']=1
        new=imports.enter_context(load(src,'_signal_packet_repaired'))
        def reject(f):
            try:f()
            except (ValueError,TypeError):counts['malformed_calls_rejected']+=1;return
            raise AssertionError('Malformed call accepted')
        branch=(new.Branch(((1,),),()),);w=new.canonical_witness(branch,(1,),(1,))
        for bad in ((1,999),(),(True,),(1.0,),(-1,)):
            reject(lambda:new.polynomial_value(branch,(1,),bad,w));reject(lambda:new.canonical_witness(branch,(1,),bad))
            reject(lambda:new.polynomial_value(branch,bad,(1,),w));reject(lambda:new.canonical_witness(branch,bad,(1,)))
        for badw in ((w[0],w[1],((None,),)),((True,),w[1],w[2]),((1.0,),w[1],w[2]),(w[0],((1,9),),w[2]),(w[0],w[1],()),(w[0],(),w[2])):
            reject(lambda:new.polynomial_value(branch,(1,),(1,),badw))
        for kind in ('oops','',None):reject(lambda:new.Guard(kind,(1,)))
        for coeff in ((True,),(1.0,)):reject(lambda:new.Guard('eq',coeff))
        reject(lambda:new.Branch(((1,2),),()));reject(lambda:new.Branch(((1,),),(new.Guard('eq',(1,2)),)))
        matrix=[[1]];coeff=[1];guards=[new.Guard('ge',coeff)];b=new.Branch(matrix,guards)
        matrix[0][0]=9;coeff[0]=8;guards.clear()
        require(b.output((3,))==(3,) and b.guards[0].coeff==(1,),'Frozen branch retained mutable caller input')
        counts['immutable_nested_snapshot_regression']=1
        rng=random.Random(2026100218)
        for case in range(200):
            branches0=(old.Branch(((0,),),(old.Guard('eq',(1,)),)),old.Branch(((2,),),(old.Guard('gt',(1,)),)))
            branches1=(new.Branch(((0,),),(new.Guard('eq',(1,)),)),new.Branch(((2,),),(new.Guard('gt',(1,)),)))
            x=(rng.randrange(5),);y=(rng.randrange(9),)
            selectors=tuple(rng.randrange(4) for _ in range(2));copies=tuple((rng.randrange(5),) for _ in range(2));slacks=((),(rng.randrange(5),))
            witness=(selectors,copies,slacks)
            require(exact(old.packet_terms(branches0,x,y,witness),new.packet_terms(branches1,x,y,witness)),'Valid residual changed')
            require(exact(old.canonical_witness(branches0,x,y),new.canonical_witness(branches1,x,y)),'Valid section changed')
            counts['unchanged_valid_full_packet_cases']+=1
        numeric=root/'numeric';machine=json.loads((numeric/'MORITA_18_SIGNAL_MACHINE.json').read_text())
        labels=sorted(machine['meta_signals']);ids={a:i for i,a in enumerate(labels)};speeds=[machine['meta_signals'][a] for a in labels]
        rules={}
        outputs=set()
        for rule in machine['collision_rules']:
            incoming=tuple(sorted((ids[a] for a in rule['incoming']),key=lambda i:-speeds[i]));outgoing=tuple(sorted((ids[a] for a in rule['outgoing']),key=lambda i:speeds[i]))
            require(len(incoming)==len(outgoing)==2 and speeds[incoming[0]]>speeds[incoming[1]] and speeds[outgoing[0]]<speeds[outgoing[1]],'Invalid rule')
            require(incoming not in rules and outgoing not in outputs,'Noninjective literal rule')
            rules[incoming]=outgoing;outputs.add(outgoing)
        require(len(labels)==114 and len(rules)==445,'Literal cardinalities changed')
        with gzip.open(numeric/'MODES.jsonl.gz','rt') as f:modes=[json.loads(line) for line in f]
        with gzip.open(numeric/'EVENTS.jsonl.gz','rt') as f:events=[json.loads(line) for line in f]
        index={tuple(m['labels']):i for i,m in enumerate(modes)};require(len(index)==len(modes),'Duplicate modes')
        outgoing={i:set() for i in range(len(modes))};graph={i:set() for i in range(len(modes))}
        for i,record in enumerate(events):
            r,s,t,pivot,mask=record;require(r==i and 0<=s<len(modes) and 0<=t<len(modes),'Malformed event')
            J=tuple(j for j in range(17) if mask>>j&1);require(J and pivot==min(J) and mask<1<<17,'Invalid tie mask')
            item=(J,t);require(item not in outgoing[s],'Duplicate event');outgoing[s].add(item);graph[s].add(t)
        for i,m in enumerate(modes):
            order=tuple(m['labels']);q=1+sum(a*114**(17-k) for k,a in enumerate(order));c=[speeds[order[k]]-speeds[order[k+1]] for k in range(17)]
            require(m['id']==i and m['q']==str(q) and m['c']==c,'Incorrect mode record')
            generated=set()
            def choices(edge,selected,labels1):
                if edge>=17:
                    if selected:
                        require(tuple(labels1) in index,'Closure missing mode');generated.add((tuple(selected),index[tuple(labels1)]))
                    return
                choices(edge+1,selected,labels1)
                pair=(order[edge],order[edge+1])
                if pair in rules:
                    changed=list(labels1);changed[edge:edge+2]=rules[pair]
                    choices(edge+2,selected+[edge],changed)
            choices(0,[],list(order));require(generated==outgoing[i],'Independent matching closure differs')
            counts['independently_complete_mode_successor_sets']+=1
        initial=tuple(ids[a] for a in machine['mode_encoding']['label_orders']['initial']);require(index[initial]==0,'Initial mode changed')
        reached={0};queue=deque([0]);depth={0:0}
        while queue:
            v=queue.popleft()
            for w1 in graph[v]:
                if w1 not in reached:reached.add(w1);depth[w1]=depth[v]+1;queue.append(w1)
        require(len(reached)==len(modes) and all(depth[i]==m['bfs_depth'] for i,m in enumerate(modes)),'Unreachable extra mode or wrong depth')
        counts['independently_reached_modes']=len(reached)
        compiler=imports.enter_context(load(numeric/'compile_packet.py','_signal_numeric_review')).Compiler().close()
        E=T=L=MN=NG=affmax=matrixmax=0;max_dense=(0,None);Jhist=Counter();min_weight=None;min_strict=None
        for r,s,t,pivot,mask in events:
            c=modes[s]['c'];q=int(modes[s]['q']);qn=int(modes[t]['q']);cj=c[pivot];J=tuple(j for j in range(17) if mask>>j&1)
            require(cj>0 and sum(c)==0,'Active endpoint assumption failed')
            expected=[]
            for i in range(17):
                row={i:cj};row[pivot]=row.get(pivot,0)-c[i];expected.append(sorted((k,v) for k,v in row.items() if v))
            expected.append([(i,cj*qn) for i in range(17)])
            require(compiler.matrix(s,t,J)==expected,'Paid matrix differs')
            eq,strict=compiler.guards(s,t,J)
            require(len(eq)==len(J) and len(strict)==sum(v>=0 for v in c)+19-len(J),'Guard ledger changed')
            weight=cj*qn;min_weight=weight if min_weight is None else min(min_weight,weight)
            strict_sum=[sum(v for _,row in strict for j,v in row if j==i) for i in range(17)]
            require(min(strict_sum)>0 and weight**2>17*24**2+1,'Expanded monomial noncancellation failed')
            min_strict=min(strict_sum) if min_strict is None else min(min_strict,min(strict_sum))
            h=[ci if i in J else max(ci,0)+1 for i,ci in enumerate(c)];X=h+[q*sum(h)]
            require(all(sum(v*X[k] for k,v in row)==0 for _,row in eq),'Equality failed')
            require(all(sum(v*X[k] for k,v in row)>0 for _,row in strict),'Strict guard failed')
            Y=[sum(v*X[k] for k,v in row) for row in expected]
            require(all(v>=0 for v in Y) and Y[17]==qn*sum(Y[:17]) and {i for i in range(17) if Y[i]==0}==set(J),'Constructive branch output failed')
            out=modes[t]['labels'];require(all(Y[i]>0 or speeds[out[i]]<speeds[out[i+1]] for i in range(17)),'Outgoing germ failed')
            require(sum(len(row) for row in expected[:17])<=32 and all(abs(v)<=24 for row in expected[:17] for _,v in row),'Gap resource bound failed')
            E+=len(eq);T+=len(strict);L+=sum(len(row) for _,row in strict);MN+=sum(len(row) for row in expected);NG+=sum(len(row) for row in expected[:17]);Jhist[len(J)]+=1
            matrixmax=max(matrixmax,max(abs(v) for row in expected for _,v in row));affmax=max(affmax,q,matrixmax)
            candidate=2*((cj*qn)**2+q*q+1+2*cj*max(0,-min(c)))
            if candidate>max_dense[0]:max_dense=(candidate,r)
            counts['independent_literal_branch_audits']+=1
        B=len(events);H=17*B
        terms=1+B+H*(H+1)//2+B*(B+1)+17*B+36+18*B+MN+18*B*(B-1)+17*B+2*T+L
        ledger=json.loads((numeric/'LEDGER.json').read_text())
        derived=dict(modes=len(modes),branches=B,equality_guards=E,strict_guards=T,weak_guards=0,strict_form_nonzeros=L,
                     auxiliary_variables=19*B+T,total_variables=36+19*B+T,affine_residuals=37+E+T,complementarity_products=B,
                     gap_matrix_nonzeros_total=NG,full_matrix_nonzeros_total=MN,affine_variable_nonzeros=35*B+36+MN+2*E+L+2*T,
                     expanded_total_nonzeros=terms,max_affine_abs=str(affmax),max_affine_bits=affmax.bit_length(),
                     expanded_max_abs_coefficient=str(max_dense[0]),expanded_max_coefficient_bits=max_dense[0].bit_length(),expanded_max_branch_id=max_dense[1])
        require(all(exact(ledger[k],v) for k,v in derived.items()),'Derived complete ledger changed')
        require(max_dense[0]>2*matrixmax**2+19586,'Cross-branch coefficient height bound failed')
        r=max_dense[1];s,t,J=compiler.branches[r];c=modes[s]['c'];i=min(range(17),key=c.__getitem__)
        require(compiler.coefficient(compiler.copy(r,J[0]),compiler.copy(r,i))==max_dense[0],'Maximum coefficient not attained')
        return dict(status='PASS_WITH_REPAIRED_GENERIC_PACKET_API',archive=ARCHIVE,arrival=ARRIVAL,archive_sha256=ARCHIVE_SHA,
                    member_sha256=members,original_packet_sha256=SOURCE_SHA,patch_sha256=PATCH_SHA,repaired_packet_sha256=REPAIRED_SHA,
                    counts=dict(counts),independent_packet_review=independent,noncancellation=dict(minimum_active_output_mode_weight=str(min_weight),minimum_strict_form_sum_coefficient=min_strict,gap_cross_term_dominance_bound=9793),derived_literal_ledger=derived,simultaneous_branch_counts={str(k):v for k,v in sorted(Jhist.items())},
                    author_receipts={k:v for k,v in saved.items() if k.startswith('receipts/') or k in ('numeric/COMPACT_VERIFICATION.json','numeric/EXPORTER_TEST_RECEIPT.json','numeric/ORIGINAL_REPLAY_AUDIT.json')},
                    scope='Literal finite event closure and quadratic step/fixed-horizon packet; original full author replay plus independent exhaustive mode/branch/ledger audit. Patch only repairs generic packet dimensions, exact scalar types and immutable snapshots. No trillion-term expansion, fixed-arity unbounded decoder, optimized gate count or new87 bound.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path);p.add_argument('--patch',type=Path);p.add_argument('--write',action='store_true');a=p.parse_args();here=Path(__file__).resolve()
    repo=a.repo or next(x for x in here.parents if (x/'.git').exists())
    result=verify(repo.resolve(),(a.patch or here.with_name('conservative_signal_packet_domains.patch')).resolve())
    dest=here.with_suffix('.json')
    if a.write:dest.write_text(json.dumps(result,indent=2)+'\n')
    else:require(exact(result,json.loads(dest.read_text())),'Saved receipt changed')
    print(json.dumps({'status':result['status'],'counts':result['counts'],'ledger':result['derived_literal_ledger']},indent=2))
