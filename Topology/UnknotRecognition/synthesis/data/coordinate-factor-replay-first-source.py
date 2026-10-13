"""Portable independent replay of two frozen coordinate-factor probes.

Archived files are authenticated as bytes. No archived main, native producer,
LP, discovery, test or timing job is executed. Current native independent
verifiers authenticate the saved chains; exact rank/circuit checks replay the
six full kernels and all 276 singleton masks.
"""
import argparse
import ast
from contextlib import contextmanager
from fractions import Fraction as F
from hashlib import sha256
import gzip
import importlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import traceback

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
REVISION = '4d1f76f061ac961ee75c4d7d8b067b5fa0ac30f7'
GIT_PREFIX = 'Topology/UnknotRecognition/'
ARCHIVE = DATA/'coordinate-factor-probes.tar.gz'
MANIFEST = DATA/'coordinate-factor-archive.json'
ARCHIVE_SHA256 = '470c2e6b02ce7c2092b89266ef37ddddffd308b857e06830f294784be6584b9a'
MANIFEST_SHA256 = '12221ce8a740d16f710b8b231a9fa8ce388eb7cf360cf0a2c361e28516378e02'
PREFIX = 'coordinate-factor-probes/'
CASES = (('circle', None, ()), ('trefoil', 2, (1,1,1)),
    ('figure_eight', 3, (1,-2,1,-2)), ('TT', 3, (1,1,1,2,2,2)),
    ('T25', 2, (1,1,1,1,1)), ('T27', 2, (1,1,1,1,1,1,1)),
    ('W34', 3, (1,-2,1,-2,1,-2,1,-2)))
TETRAHEDRA = (7,10,16,11,17,31)
WITNESS_DIR = ROOT/'fast/conditional_type_research/data/conditional-type-witnesses'
WITNESS_HASHES = {
    'probe.json.gz': ('b7b57229b8587ec99c4c13a5c83bd0cd758f66c5b805abf45517a0d95be871db',
        'fac010b3fa73dcdb4733b2a3d4f3a39906c28baee062598230a79de85ed8c0bd'),
    'replay.json.gz': ('748fb00e7d2af9b6f02194df3cfb82bc7aa3046cfa4a77c21a8a5a4760b597b1',
        'b42a1487358e45feb1ff686bf07bb3a2b6c249a7b59ab772e8288c65e6695344'),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(same(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):
        return len(a) == len(b) and all(same(x,y) for x,y in zip(a,b))
    return a == b


def safe(value):
    if type(value) is F:
        return [value.numerator,value.denominator]
    if type(value) in (tuple,list):
        return [safe(x) for x in value]
    if type(value) is dict:
        return {k:safe(v) for k,v in value.items()}
    return value


def canonical(value):
    return json.dumps(safe(value),sort_keys=True,separators=(',',':')).encode()


def digest(value):
    return sha256(canonical(value)).hexdigest()


def equal(a,b,message):
    require(same(a,b),message)


def save(path,result):
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_bytes(canonical(result)+b'\n')
    temporary.replace(path)


def current_pins():
    paths=set((ROOT/'fast/fastunknot').rglob('*.py'))
    paths.update((ARCHIVE,MANIFEST,Path(__file__).resolve(),
                  DATA/'geometric-descent-audit.json'))
    paths.update(WITNESS_DIR/name for name in WITNESS_HASHES)
    return {str(path.relative_to(ROOT)):sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def archive_members():
    require(sha256(MANIFEST.read_bytes()).hexdigest()==MANIFEST_SHA256,'archive manifest bytes')
    manifest=json.loads(MANIFEST.read_bytes())
    equal(manifest['schema'],'coordinate-factor-archive-v1','archive manifest schema')
    equal(manifest['historical_revision'],REVISION,'historical source revision')
    raw=ARCHIVE.read_bytes()
    require(len(raw)==319368 and sha256(raw).hexdigest()==ARCHIVE_SHA256,'exact preserved archive bytes')
    equal(manifest['archive'],ARCHIVE.name,'archive name')
    equal(manifest['archive_sha256'],ARCHIVE_SHA256,'archive manifest digest')
    equal(manifest['archive_bytes'],len(raw),'archive manifest size')
    expected={PREFIX+'full/'+name for name in ('probe.py','probe.json','probe.txt','HANDOFF.md')}
    expected.update(PREFIX+'singleton/'+name for name in
        ('common.py','probe.py','replay.py','probe.json','replay.json','probe.txt','replay.txt','HANDOFF.md'))
    equal(set(manifest['files']),expected,'exact provenance inventory')
    payloads={}
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as handle:
        members=handle.getmembers()
        require(len(members)==12 and len({item.name for item in members})==12,'unique twelve regular members')
        equal([item.name for item in members],sorted(expected),'canonical archive order')
        for item in members:
            name=PurePosixPath(item.name)
            require(not name.is_absolute() and '..' not in name.parts and '\\' not in item.name and
                    str(name)==item.name and item.name.startswith(PREFIX),'safe canonical archive member')
            require(item.isfile() and item.type==tarfile.REGTYPE and not item.pax_headers and
                    item.uid==item.gid==item.mtime==0 and item.mode==0o644 and
                    item.uname==item.gname=='','regular immutable archive metadata')
            require(0<=item.size<=5971876,'bounded archive member size')
            content=handle.extractfile(item).read()
            metadata=manifest['files'][item.name]
            require(len(content)==item.size==metadata['bytes'] and sha256(content).hexdigest()==metadata['sha256'],'exact original member bytes')
            payloads[item.name[len(PREFIX):]]=content
    equal(manifest['member_count'],12,'archive member count')
    equal(manifest['member_bytes'],sum(map(len,payloads.values())),'archive raw byte total')
    require(sum(map(len,payloads.values()))==5971876,'fixed raw byte total')
    return payloads,manifest


def definitions(raw,names,namespace,label):
    """Load only named function definitions; never archived imports or mains.

    rank/rational/replay_mask are the completed independent scratch replayer,
    not its partition producer. The native-discovery guard and original-row
    lift checker are similarly loaded without any archived path constants.
    """
    parsed=ast.parse(raw,filename=label)
    selected=[node for node in parsed.body if isinstance(node,ast.FunctionDef) and node.name in names]
    equal({node.name for node in selected},set(names),'exact selected function definitions')
    require(len(selected)==len(names),'unique selected definitions')
    module=ast.Module(body=selected,type_ignores=[])
    exec(compile(module,label,'exec'),namespace)
    return namespace


def historical_binding(full,singleton,replayed,payloads):
    """Authenticate old dependencies at old revision, not as current code."""
    equal(full['repository_head'],REVISION,'original executed HEAD')
    original=full['source_sha256']
    native={k:v for k,v in original.items() if k.startswith('fast/fastunknot/') and k.endswith('.py')}
    require(len(native)==299 and len(original)==301,'original native/dependency coverage')
    audit_name='synthesis/data/geometric-descent-audit.json'
    script_name='/tmp/euler-coordinate-factor-probe/probe.py'
    equal(set(original),set(native)|{audit_name,script_name},'exact historical dependency set')
    require(original[script_name]==sha256(payloads['full/probe.py']).hexdigest(),'executed full-probe code pin')
    raw=subprocess.check_output(['git','archive','--format=tar',REVISION,
        GIT_PREFIX+'fast/fastunknot',GIT_PREFIX+audit_name],cwd=ROOT)
    historical={}
    audit_bytes=None
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r:') as handle:
        for member in handle.getmembers():
            if not member.isfile():
                continue
            name=member.name[len(GIT_PREFIX):]
            data=handle.extractfile(member).read()
            if name.startswith('fast/fastunknot/') and name.endswith('.py'):
                historical[name]=sha256(data).hexdigest()
            elif name==audit_name:
                audit_bytes=data
    equal(historical,native,'committed historical native byte map')
    require(audit_bytes is not None and sha256(audit_bytes).hexdigest()==original[audit_name],'committed historical audit dependency')
    require((ROOT/audit_name).read_bytes()==audit_bytes,'maintained retained audit bytes')
    require(full['input_audit_sha256']==original[audit_name],'executed audit digest')
    audit=json.loads(audit_bytes)
    equal(full['historical_audit_source_pins'],audit['source_sha256'],'prior audit generation metadata retained')
    equal(full['historical_pins_compared_to_current'],False,'historical audit pins not relabelled current')
    expected=dict(original_probe_path='/tmp/euler-coordinate-factor-probe/probe.json',
        original_probe_sha256=sha256(payloads['full/probe.json']).hexdigest(),
        original_probe_code_path=script_name,original_probe_code_sha256=original[script_name],
        original_source_sha256=original,scratch_source_sha256={name:sha256(payloads['singleton/'+name]).hexdigest()
            for name in ('common.py','probe.py','replay.py')})
    equal(singleton['pins'],expected,'singleton execution input/code bindings')
    equal(replayed['pins'],expected,'singleton historical replay bindings')
    require(replayed['input_sha256']==sha256(payloads['singleton/probe.json']).hexdigest(),'historical singleton replay exact input')
    return audit


def check_full_algebra(algebra,source,model,prepared,functions):
    matrix,linear,groups,potentials,weights=model
    matrix=[list(row) for row in matrix]
    t=len(source['tetrahedra']); n=3*t
    columns=list(range(n))
    equal(algebra['matrix'],matrix,'fresh original STANDARD-derived Q matrix')
    require(algebra['matrix_sha256']==digest(matrix),'raw full matrix digest')
    equal(algebra['allowed_types'],[[i,j] for i in range(t) for j in range(3)],'complete full Q mask')
    equal(algebra['original_standard_matching'],[[[i,a] for i,a in sorted(row.items())] for row in prepared['matching']],'original matching rows')
    equal(algebra['euler_model'],safe(dict(linear=linear,groups=groups,weights=weights,
        potentials=[dict(corner_class=c,coefficients=row) for c,row in sorted(potentials.items())])), 'source Euler potential model')
    rank=functions['rank']; rational=functions['rational']
    r=rank(matrix,columns)
    equal(algebra['rank'],r,'independent full rank')
    equal(algebra['nullity'],n-r,'independent full nullity')
    pivots=algebra['pivot_columns']
    require(type(pivots) is list and all(type(j) is int for j in pivots) and pivots==sorted(set(pivots)) and
            set(pivots)<=set(columns) and len(pivots)==r and rank(matrix,pivots)==r,'full pivot basis')
    reduced=[[rational(v) for v in row] for row in algebra['rref']]
    transform=[[rational(v) for v in row] for row in algebra['rref_row_transformation']]
    require(len(reduced)==len(transform)==r and all(len(row)==n for row in reduced) and
            all(len(row)==len(matrix) for row in transform),'RREF transformation dimensions')
    for i,(row,coefficients) in enumerate(zip(reduced,transform)):
        for j in columns:
            require(sum(a*original[j] for a,original in zip(coefficients,matrix))==row[j],'saved RREF exact original row combination')
        require(all(row[p]==int(i==k) for k,p in enumerate(pivots)),'saved RREF pivot identity')
    free=[j for j in columns if j not in pivots]
    circuits=algebra['nullspace_fundamental_circuits']
    require(len(circuits)==len(free),'full nullspace dimension coverage')
    graph={j:set() for j in columns}; active=set(); vectors=[]
    for item,j in zip(circuits,free):
        equal(item['free_column'],j,'ordered full fundamental basis')
        vector=[rational(v) for v in item['vector']]
        require(len(vector)==n and vector[j]==1 and all(vector[k]==0 for k in free if k!=j),'free-coordinate identity')
        support=[k for k,v in enumerate(vector) if v]
        equal(item['support'],support,'exact full circuit support')
        require(all(sum(a*b for a,b in zip(row,vector))==0 for row in matrix),'full circuit original equations')
        for k in support:
            graph[j].add(k); graph[k].add(j)
        active.update(support); vectors.append((j,vector))
    partition=[]; unseen=set(columns)
    while unseen:
        queue=[min(unseen)]; reached=set(queue)
        for j in queue:
            for k in graph[j]:
                if k not in reached:
                    reached.add(k); queue.append(k)
        unseen-=reached; partition.append(sorted(reached))
    components=algebra['components']
    equal([c['columns'] for c in components],partition,'finest full column-matroid components')
    zero=[j for j in columns if all(row[j]==0 for row in matrix)]
    forced=[j for j in columns if j not in active]
    equal(algebra['zero_columns_free_loops'],zero,'full zero-column loops')
    equal(algebra['forced_zero_columns_coloops'],forced,'full forced-zero coloops')
    ranks=[]
    for index,(component,block) in enumerate(zip(components,partition)):
        localrank=rank(matrix,block); ranks.append(localrank)
        expected=dict(index=index,columns=block,allowed_types=[[j//3,j%3] for j in block],
            tetrahedra=sorted({j//3 for j in block}),rank=localrank,nullity=len(block)-localrank,
            kind='free_loop' if len(block)==1 and block[0] in zero else 'nontrivial_matroid_component',
            fundamental_free_columns=[j for j in free if j in block])
        for key,value in expected.items():
            equal(component[key],value,'full component '+key)
        indicator=[int(j in block) for j in columns]
        equal(component['strictly_positive_kernel_witness'],indicator,'component positive kernel indicator')
        require(all(sum(a*b for a,b in zip(row,indicator))==0 for row in matrix),'indicator original kernel')
        lift=functions['canonical_lift'](prepared,indicator,model,lambda:None)
        equal(component['witness_lift'],safe(lift),'original STANDARD canonical indicator replay')
        samples=[]
        for j,vector in vectors:
            if j in block and all(v>=0 for v in vector):
                observation=functions['canonical_lift'](prepared,vector,model,lambda:None)
                if observation['formal_euler']>0:
                    samples.append(dict(free_column=j,quadrilaterals=vector,**observation))
        equal(component['sampled_positive_euler_witnesses'],safe(samples),'sampled Euler diagnostic replay')
        equal(component['euler_positivity_classification'],'witness_found' if lift['formal_euler']>0 or samples else 'undetermined_without_further_analysis','Euler scope')
        equal(component['nonnegative_capable'],True,'positive indicator capability only')
    require(sum(ranks)==r,'full independent rank additivity')
    local=[]
    for tet in range(t):
        block=list(range(3*tet,3*tet+3))
        require(all(sum(row[j] for j in block)==0 for row in matrix),'tetrahedral block-ones relation')
        local.append(dict(tetrahedron=tet,columns=block,nonzero_columns=[j for j in block if j not in zero],block_ones_in_kernel=True))
    equal(algebra['tetrahedral_block_ones_relations'],local,'all local kernel relations')
    scalar=dict(tetrahedra=t,vertices=prepared['vertices'],boundary_faces=len(prepared['boundary_faces']),
        component_count=len(partition),nonnegative_capable_component_count=len(partition),
        nontrivial_component_count=sum(c['kind']!='free_loop' for c in components),
        component_tetrahedron_counts=[len(c['tetrahedra']) for c in components],
        signed_kernel_coordinate_direct_sum_checked=True,rank_additivity_checked=True,
        full_nonnegative_cone_coordinate_product_checked=True,euler_positive_component_classification_complete=False)
    for key,value in scalar.items():
        equal(algebra[key],value,'full algebra summary '+key)
    require(len(partition)==1 and not zero and not forced,'retained full no-split observation')
    return dict(tetrahedra=t,rank=r,nullity=n-r,component_count=len(partition),
        nonnegative_capable_component_count=len(partition),nontrivial_component_count=scalar['nontrivial_component_count'],
        component_tetrahedron_counts=scalar['component_tetrahedron_counts'],zero_columns_free_loops=zero,forced_zero_columns_coloops=forced)


def witness_source_bindings(full):
    """Bind old verified matching witnesses to these exact sources, no rerun.

    This rechecks source/PD identity and archive integrity only. The previous
    witness audit is retained evidence, not a new matching or Euler query.
    """
    documents={}
    files={}
    for name,(stored_hash,raw_hash) in WITNESS_HASHES.items():
        path=WITNESS_DIR/name
        stored=path.read_bytes()
        require(sha256(stored).hexdigest()==stored_hash,'old matching witness stored bytes')
        uncompressed=gzip.decompress(stored)
        require(sha256(uncompressed).hexdigest()==raw_hash,'old matching witness original bytes')
        documents[name]=json.loads(uncompressed)
        files[str(path.relative_to(ROOT))]=dict(stored_sha256=stored_hash,raw_sha256=raw_hash)
    old=documents['probe.json.gz']; replay=documents['replay.json.gz']
    equal(old['schema'],'scratch-conditional-type-witnesses-v1','prior matching witness schema')
    equal(old['passed'],True,'prior successful matching construction')
    equal(replay['passed'],True,'retained prior matching replay')
    equal(replay['probe_sha256'],WITNESS_HASHES['probe.json.gz'][1],'prior matching replay input')
    equal(replay['verified_matching_witnesses'],276,'retained prior witness coverage')
    equal(replay['all_initial_conditional_types_feasible'],True,'prior matching conclusion')
    require(len(old['records'])==6,'six previous witness sources')
    bindings=[]
    for previous,current,old_name,t in zip(old['records'],full['records'][1:],
            ('T','F','TT','T25','T27','W34'),TETRAHEDRA):
        equal(previous['id'],old_name,'prior matching case order')
        equal(previous['source'],current['source'],'typed source equality with old matching witnesses')
        equal(previous['input_pd'],current['input_pd'],'typed PD equality with old matching witnesses')
        require(previous['source_sha256']==current['source_sha256']==digest(previous['source']),'matching witness exact source digest')
        equal(previous['full_initial_mask'],[[a,b] for a in range(t) for b in range(3)],'prior full mask')
        equal(previous['all_types_have_matching_witnesses'],True,'prior per-source matching coverage')
        require(len(previous['queries'])==3*t,'prior matching target count')
        bindings.append(dict(id=current['id'],prior_id=old_name,source_sha256=current['source_sha256'],
            typed_source_equal=True,typed_pd_equal=True,prior_matching_witnesses=3*t))
    return dict(source_bindings=bindings,files=files,exact_source_bindings=6,
        prior_matching_witnesses=276,prior_matching_witnesses_replayed_here=False,
        matching_feasibility_bound_to_prior_verified_evidence=True,
        positive_euler_established_by_this_binding=False)


def check(log_progress=lambda phase:None):
    before=current_pins()
    payloads,manifest=archive_members()
    full=json.loads(payloads['full/probe.json'])
    singleton=json.loads(payloads['singleton/probe.json'])
    old_replay=json.loads(payloads['singleton/replay.json'])
    for document in (full,singleton,old_replay):
        equal(document['passed'],True,'retained successful execution')
        equal(document['errors'],[],'no retained error')
        equal(document['active'],None,'no unreturned active operation')
        equal(document['source_pins_unchanged'],True,'retained unchanged input pins')
    equal(full['schema'],'scratch-euler-coordinate-factor-probe-v1','full schema')
    equal(singleton['schema'],'scratch-euler-one-tet-separator-v1','singleton schema')
    equal(old_replay['schema'],'scratch-euler-one-tet-separator-replay-v1','old independent replay schema')
    equal(full['coverage'],dict(authenticated_chains=7,terminal_sources=1,full_q_matrices=6),'full coverage')
    equal(singleton['expected_masks'],276,'declared singleton coverage')
    equal(singleton['records_completed'],276,'completed singleton coverage')
    equal(old_replay['coverage'],dict(sources=6,singleton_masks=276,independent_rank_additivity_checks=276),'historical independent replay coverage')
    audit=historical_binding(full,singleton,old_replay,payloads)
    matching_bindings=witness_source_bindings(full)
    log_progress('current_native_chain_and_full_matrix_replay')
    sys.path.insert(0,str(ROOT/'fast'))
    from fastunknot.diagram import Diagram
    from fastunknot.normal_crushing_chain import verify_crushing_chain
    from fastunknot.normal_crushing_search import verify_crushing_recognition
    from fastunknot.normal_surface_geometry import _prepare,_EDGES,_quad
    from fastunknot.normal_euler_verify import _reference_model
    namespace=dict(require=require,same=same,F=F,contextmanager=contextmanager,
        importlib=importlib,sys=sys,_EDGES=_EDGES,_quad=_quad)
    functions=definitions(payloads['full/probe.py'],
        ('discovery_disabled','dot','canonical_lift'),namespace,'archived:full/probe.py')
    definitions(payloads['singleton/replay.py'],('rank','rational','replay_mask'),functions,'archived:singleton/replay.py')
    definitions(payloads['singleton/common.py'],('summarize',),functions,'archived:singleton/common.py')
    equal(full['fixed_case_order'],[case[0] for case in CASES],'fixed seven-case order')
    equal(audit['case_order'],full['fixed_case_order'],'original whole-call order')
    require(len(full['records'])==len(audit['records'])==7 and len(singleton['sources'])==6,'exact record coverage')
    summary=[]; full_log=[]; source_inputs=[]
    with functions['discovery_disabled']() as disabled:
        for index,(case,retained,actual) in enumerate(zip(CASES,full['records'],audit['records'])):
            name,strands,word=case
            diagram=Diagram.from_pd([]) if strands is None else Diagram.from_braid(strands,word)
            pd=[list(row) for row in diagram.pd]
            equal(retained['id'],name,'full source order')
            equal(actual['id'],name,'audit source order')
            equal(retained['input_pd'],pd,'literal input PD')
            equal(actual['input_pd'],pd,'audit input PD')
            require(retained['input_pd_sha256']==actual['input_pd_sha256']==digest(pd),'PD digest')
            whole=actual['arms']['geometric']['result']
            chain=whole['partial_chain'] if whole['status']=='INCONCLUSIVE' else whole['certificate']['chain']
            equal(retained['chain'],chain,'byte-authenticated retained full chain')
            equal(retained['saved_status'],whole['status'],'retained original status')
            require(retained['saved_result_sha256']==digest(whole) and retained['chain_sha256']==digest(chain),'whole-result and chain digests')
            if whole['status']=='INCONCLUSIVE':
                require(verify_crushing_chain(diagram,chain),'current independent partial chain replay')
            else:
                require(verify_crushing_recognition(diagram,whole['certificate']),'current independent conclusive recognition replay')
            equal(retained['chain_verified'],True,'historical chain flag')
            equal(retained['conclusive_recognition_replayed'],whole['status']!='INCONCLUSIVE','historical replay scope')
            source=chain['triangulation']; terminal=source is None
            equal(retained['source'],source,'exact authenticated endpoint')
            equal(retained['terminal'],terminal,'terminal endpoint flag')
            equal(retained['source_sha256'],None if terminal else digest(source),'exact source digest')
            if terminal:
                require(name=='circle' and whole['status']=='UNKNOT','only terminal circle')
                equal(retained['algebra'],None,'no terminal matrix')
                result=dict(id=name,source_sha256=None,terminal=True)
            else:
                prepared=_prepare(source,lambda:None)
                t=len(source['tetrahedra'])
                equal(t,TETRAHEDRA[index-1],'fixed source size')
                require(prepared['vertices']==1 and len(prepared['boundary_faces'])==2,'finite one-vertex endpoint geometry')
                model=_reference_model(prepared,tuple((a,b) for a in range(t) for b in range(3)),lambda:None)
                algebra=check_full_algebra(retained['algebra'],source,model,prepared,functions)
                result=dict(id=name,source_sha256=digest(source),terminal=False,**algebra)
                source_inputs.append(dict(id=name,tetrahedra=t,source_sha256=digest(source),
                    matrix_sha256=digest([list(row) for row in model[0]]),original_columns=3*t,
                    original_rank=algebra['rank'],original_nullity=algebra['nullity'],
                    matrix_rows=len(model[0]),matrix=[list(row) for row in model[0]]))
            summary.append(result)
            full_log.append(dict(id=name,terminal=terminal,tetrahedra=None if terminal else t,
                components=None if terminal else algebra['component_count'],
                component_tetrahedron_counts=None if terminal else algebra['component_tetrahedron_counts']))
        equal(full['summary'],summary,'fresh full summary')
        log_progress('all_276_mask_partitions')
        replay_records=[]; singleton_log=[]; replay_log=[]
        for source,saved in zip(source_inputs,singleton['sources']):
            equal({k:v for k,v in saved.items() if k!='records'},
                  {k:v for k,v in source.items() if k!='matrix'},'restricted source and matrix binding')
            require(len(saved['records'])==3*source['tetrahedra'],'all ordered singleton assignments')
            for number,record in enumerate(saved['records']):
                tet,typ=divmod(number,3)
                replay=functions['replay_mask'](source,record,tet,typ)
                replay_records.append(dict(id=source['id'],**replay))
                require(record['component_count']==1 and record['largest_noncoloop_component_size']==source['original_columns']-2 and
                        record['forced_zero_columns_coloops']==[] and record['zero_columns_free_loops']==[], 'retained singleton no-split observation')
            singleton_log.append(dict(id=source['id'],masks=len(saved['records']),summary=functions['summarize']([saved])[0]))
            replay_log.append(dict(id=source['id'],replayed_masks=len(saved['records'])))
        require(len(replay_records)==276,'complete fresh rank/circuit replay')
        equal(old_replay['records'],replay_records,'every historical independent replay record')
        singleton_summary=functions['summarize'](singleton['sources'])
        equal(singleton['summary'],singleton_summary,'fresh restricted summary')
        equal(old_replay['summary'],singleton_summary,'historical replay summary')
    full_log.append(dict(passed=True,coverage=full['coverage'],summary=summary))
    singleton_log.append(dict(passed=True,records_completed=276,summary=singleton_summary))
    replay_log.append(dict(passed=True,coverage=old_replay['coverage'],summary=singleton_summary))
    for name,expected in (('full/probe.txt',full_log),('singleton/probe.txt',singleton_log),('singleton/replay.txt',replay_log)):
        equal([json.loads(line) for line in payloads[name].splitlines()],expected,'complete raw stdout binding '+name)
    require(full['callback_checks']==sum(record['callback_checks'] for record in full['records']) and
            all(type(record['callback_checks']) is int and record['callback_checks']>=0 for record in full['records']),'retained callback arithmetic, not operation replay')
    equal(current_pins(),before,'current native and evidence bytes unchanged during replay')
    return dict(schema='coordinate-factor-portable-replay-v1',passed=True,
        historical_revision=REVISION,historical_native_files_authenticated=299,
        historical_dependency_pins_authenticated=301,archive_sha256=ARCHIVE_SHA256,
        archive_member_count=12,archive_member_bytes=manifest['member_bytes'],
        coverage=dict(authenticated_chains=7,terminal_sources=1,full_q_matrices=6,singleton_masks=276),
        full_summary=summary,singleton_summary=singleton_summary,
        prior_matching_witness_source_binding=matching_bindings,
        disabled_discovery_hooks=disabled,current_source_sha256=before,
        current_native_geometry_replay=True,current_independent_rank_replay=True,
        archived_mains_executed=False,archived_native_imported=False,
        original_scripts_regenerated=False,lp_queries=0,recognition_discovery=False,
        timings_claimed=False,nonnegative_feasibility_inferred_for_restricted_masks=False,
        general_quasipolynomial=False,errors=[])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=DATA/'coordinate-factor-replay.json')
    args=parser.parse_args()
    require(not args.output.exists(),'refuse to overwrite retained replay')
    status=dict(schema='coordinate-factor-portable-replay-v1',passed=False,phase='archive_validation',errors=[])
    save(args.output,status)
    def phase(value):
        status['phase']=value
        save(args.output,status)
    try:
        result=check(phase)
        result['phase']='complete'
        save(args.output,result)
        print(json.dumps({k:v for k,v in result.items() if k not in
            ('current_source_sha256','disabled_discovery_hooks','singleton_summary')},sort_keys=True))
    except BaseException as error:
        status['errors'].append(dict(type=type(error).__name__,message=str(error),traceback=traceback.format_exc()))
        save(args.output,status)
        raise


if __name__=='__main__':
    main()
