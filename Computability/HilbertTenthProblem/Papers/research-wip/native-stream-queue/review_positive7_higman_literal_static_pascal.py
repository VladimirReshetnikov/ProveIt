"""Original literal-template comparator. UNRUN: root preflight is mandatory.

Word arrays are strings of signed names. Only spelling, indexing, hashing and
record comparison occur: no reduction, word-problem test or machine execution.
"""
from pathlib import Path
import hashlib
import json
import traceback

TMP = Path('/tmp')
OUT = TMP / 'review_positive7_higman_literal_static_pascal.json'
if OUT.exists():
    raise RuntimeError('First audit result already exists. Never replay.')
PINS = {
    'positive7_higman_literal_presentation_riemann.md': '80ca2167b8c0eb82bf6049f7aa509b04e65f73ddded32602479ced3b8c0a8187',
    'positive7_higman_literal_presentation_riemann_provenance.json': 'f2e5f36a8038caa724c0999a90e3957ac312c1e591a599e79e1c3aced0d6d989',
    'positive7_higman_literal_presentation_riemann_first_run.txt': '14dabd0b9a7777463cc749e682245afc694176c9892778be143d21cefd76883e',
    'positive7_higman_literal_presentation_riemann.py': 'fedc405f68dda9125f94021ef7e6e08c89ba99451ed5b35aea55b761560f5d15',
    'positive7_higman_literal_presentation_riemann.json': '35a24f7ff3878f132e9bb37fa76a0c21de31795c2f72ea9e497c5efb7d1c1a57',
    'positive7_higman_benign_recipes_aristotle.md': '826c85fe63f3c2cd8f9df2b43efa3f4a7fc098db5552bbf494d41e5c0150c07c',
    'positive7_higman_shared_ambient_aristotle.md': '12692f7c9037bef148e7a9cb7788c78465745b797889ebed4098da415b24c562',
    'positive7_higman_shared_schedule_riemann.md': 'b06d3356c9960604580e3f31eae64641b35dda7129560c43764dea8ad9019526',
    'positive7_affine_typed_recognizer_pascal.md': '78e26e7b637378c5568a7da1127f5b39996572d3f254c3a65bf0065ffb61fcd0',
    'positive7_higman_affine_line_transducer_aristotle.md': 'e431ab657885f06502be8685cbdd2cef92fe65c75e3d8692b8302aac355dc42f',
}
REPORT = {'status': 'STARTED', 'scope': 'Independent preembedding literal records only; no Section7 embedding.',
          'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'bindings': []}
ROLES = ('a', 'b', 'c', 't', 't_prime', 'u1', 'u2', 'd', 'e')


def demand(condition, explanation):
    if not condition:
        raise AssertionError(explanation)


def normal(value):
    if isinstance(value, (tuple, list)):
        return [normal(item) for item in value]
    if isinstance(value, dict):
        return {key: normal(item) for key, item in value.items()}
    return value


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()


def reverse(word):
    return tuple(-token for token in word[::-1])


def repeat(word, number):
    return (word if number >= 0 else reverse(word)) * abs(number)


def con(word, by):
    return reverse(by) + word + by


def indexed(letter, shifter, number):
    return con(letter, repeat(shifter, number))


def spelling(letter, shifter, entries):
    demand(list(entries) == sorted(entries), 'increasing affine coordinate prescription')
    demand(len({i for i, _ in entries}) == len(entries), 'unique affine coordinates')
    result = ()
    for position, exponent in entries:
        result += repeat(indexed(letter, shifter, position), exponent)
    return result


class Comparator:
    """Consumes one author record only after deriving its full expected record."""
    def __init__(self, data):
        self.data = data
        self.g = 0; self.r = 0; self.event = 0
        self.mark = (); self.A = {}; self.shift = (); self.cache = {}
        self.names = set(); self.used = set(); self.letters = 0
        self.event_summaries = []

    def state(self):
        return {'g': self.g, 'r': self.r, 'marker_ids': self.mark,
                'tracked_A': self.A.copy(), 'global_shift_word': self.shift,
                'cache_fingerprints': [{'name': name, 'length': len(words), 'sha256': digest(words)}
                                       for name, words in self.cache.items()]}

    def open(self, label, kind, inputs=(), detail=None):
        demand(all(name in self.cache for name in inputs), 'cached event inputs')
        self.event += 1
        self.context = {'id': self.event, 'label': label, 'kind': kind, 'inputs': list(inputs),
                        'detail': {} if detail is None else detail, 'before': self.state()}
        self.created = []

    def end(self, selected=None, checkpoint=None):
        before = self.context['before']; after = self.state()
        if checkpoint is not None:
            demand((self.g, self.r, len(self.cache[selected])) == checkpoint, 'hand checkpoint ' + self.context['label'])
        self.context.update(after=after, selected=selected,
                            new_generator_ids=list(range(before['g']+1, self.g+1)),
                            relator_interval=[before['r'], self.r],
                            created_lists={key: self.cache[key] for key in self.created},
                            asserted_checkpoint=checkpoint)
        demand(normal(self.context) == self.data['trace'][self.event-1], 'entire event record ' + self.context['label'])
        self.event_summaries.append({'label': self.context['label'], 'g': self.g, 'r': self.r,
                                     'selected_words': None if selected is None else len(self.cache[selected])})

    def declare(self, role):
        name = self.context['label'] + '/' + role
        demand(name not in self.names, 'fresh generator namespace ' + name)
        self.g += 1; self.names.add(name)
        expected = {'id': self.g, 'name': name, 'event': self.event, 'declared_after_relator': self.r}
        demand(expected == self.data['generators'][self.g-1], 'generator record ' + name)
        return (self.g,)

    def relation(self, family, stable, source, target):
        demand(len(stable) == 1 and stable[0] > 0, 'declared stable generator')
        word = reverse(stable) + source + stable + reverse(target)
        demand(all(type(x) is int and 0 < abs(x) <= self.g for x in word), 'word name availability')
        expected = {'index': self.r, 'event': self.event, 'family': family,
                    'stable': stable, 'source': source, 'target': target, 'word': word}
        demand(normal(expected) == self.data['relators'][self.r], 'literal relation ' + self.context['label'] + ':' + family)
        self.r += 1; self.letters += len(word); self.used.update(abs(x) for x in word)

    def fixes(self, family, stable, words):
        for i, word in enumerate(words):
            self.relation(family+'/'+str(i), stable, word, word)

    def centralizer(self, role, words):
        t = self.declare(role); self.fixes(role, t, words); return t

    def maps(self, role, sources, targets):
        demand(len(sources) == len(targets), 'map list lengths')
        t = self.declare(role)
        for i in range(len(sources)):
            self.relation(role+'/'+str(i), t, sources[i], targets[i])
        return t

    def save(self, name, words):
        demand(name not in self.cache, 'new cache key')
        self.cache[name] = tuple(words); self.created.append(name)

    def markers(self):
        return tuple((x,) for x in self.mark)

    def A20(self, prefix, markers=None):
        image = {} if markers is None else dict(zip(ROLES[:3], markers))
        for role in ROLES:
            if role not in image: image[role] = self.declare(prefix+'/'+role)
        a,b,c,t,tp,u1,u2,d,e = (image[key] for key in ROLES)
        self.relation(prefix+'/b_t', t,b,b)
        self.relation(prefix+'/b_t_prime', tp,b,con(b,reverse(c)))
        self.relation(prefix+'/c_t', t,c,repeat(c,2))
        self.relation(prefix+'/c_t_prime', tp,c,repeat(c,2))
        self.fixes(prefix+'/u1', u1,(con(b,c),t,tp))
        self.fixes(prefix+'/u2', u2,(a,b,t,tp))
        self.fixes(prefix+'/d_fixed', d,tuple(con(x,u1) for x in (a,b,c)))
        for i,(x,y) in enumerate(zip((a,b,c),(con(a,b+u2),con(b,u2),con(c,b+u2)))):
            self.relation(prefix+'/d_map/'+str(i), d,con(x,u2),y)
        for i,(x,y) in enumerate(zip((a,b,c),(a,con(b,c),c))):
            self.relation(prefix+'/e/'+str(i), e,x,y)
        return image

    def start(self):
        self.open('initial','A_and_global_shift')
        self.A = self.A20('A'); self.mark = tuple(self.A[x][0] for x in ('a','b','c'))
        a,b,c = self.markers()
        self.shift = self.maps('global_s',(a,b,c),(a,con(b,c),c))
        self.end()

    def affine(self, label, offset, directions, description):
        self.open(label,'affine_leaf',detail={'offset':offset,'directions':directions,
                  'description':description,'basis':'literal tracked_A images'})
        anchor = con(self.A['a'],spelling(self.A['b'],self.A['c'],offset))
        self.save(label,(anchor,)+tuple(spelling(self.A['d'],self.A['e'],v) for v in directions))
        self.end(label)

    def moved(self,label,source,number):
        by = repeat(self.shift,number)
        self.open(label,'fixed_shift',(source,),{'exponent':number,'conjugator':by})
        self.save(label,tuple(con(w,by) for w in self.cache[source])); self.end(label)

    def combine(self,label,left,right,is_union,checkpoint=None):
        self.open(label,'union' if is_union else 'intersection',(left,right))
        t1 = self.centralizer('v1',self.cache[left]); t2 = self.centralizer('v2',self.cache[right])
        marker = self.markers()
        words = tuple(con(x,t1) for x in marker)+tuple(con(x,t2) for x in marker) if is_union else tuple(con(x,t1+t2) for x in marker)
        self.save(label,words); self.end(label,checkpoint)

    def carry(self,old,new):
        old_keys = tuple(self.cache)
        t = self.maps('persistent_transport',old,new)
        self.cache = {key:tuple(con(x,t) for x in words) for key,words in self.cache.items()}
        self.A = {key:con(x,t) for key,x in self.A.items()}; self.shift = con(self.shift,t)
        self.mark = tuple(x[0] for x in new)
        self.context['detail']['persistent_transport'] = {'stable':t,'old_marker':old,'new_marker':new,
            'transported_cache_names':old_keys,'tracked_A_rule':'conjugate all nine literal words; no marker-alias substitution',
            'new_output_excluded':True}

    def reflect(self,label,source,checkpoint):
        self.open(label,'rho',(source,)); selected = self.cache[source]; old = self.markers()
        bar = self.A20('bar_A',old); left = tuple(range(1,self.g+1))
        fresh = self.A20('fresh_A'); fresh_words = tuple(fresh[x] for x in ROLES)
        for ident in left:
            for j,y in enumerate(fresh_words):
                self.relation('direct_product/'+str(ident)+'/'+str(j),(ident,),y,y)
        v1 = self.centralizer('v1',(bar['a']+fresh['a'],bar['d']+fresh['d'],bar['e']+reverse(fresh['e'])))
        v2 = self.centralizer('v2',selected+(fresh['a'],fresh['d'],fresh['e']))
        bases = tuple(bar[x] for x in ROLES)+fresh_words
        graph = tuple(con(x,v1+v2) for x in bases); new = tuple(fresh[x] for x in ('a','b','c')); six = new+old
        w1 = self.centralizer('w1',old); w2 = self.centralizer('w2',graph)
        w3 = self.centralizer('w3',new)
        w4 = self.centralizer('w4',tuple(con(x,w1) for x in six)+tuple(con(x,w2) for x in six))
        result = tuple(con(x,w3+w4) for x in six)
        self.context['detail'].update(input_role_aliases=dict(zip(('abar','bbar','cbar'),old)),
                 bar_A=bar,fresh_A=fresh,product_left_ids=left,graph_base=bases,graph_list=graph,C6=six)
        self.carry(old,new); self.save(label,result); self.end(label,checkpoint)

    def liberate(self,label,source,checkpoint):
        self.open(label,'pi',(source,)); selected = self.cache[source]
        aux = self.A20('A_star',self.markers()); d,e = aux['d'],aux['e']
        x = self.maps('x',(d,e),(d,repeat(e,2)))
        xp = self.maps('x_prime',(d,e),(indexed(d,e,-1),repeat(e,2)))
        base = tuple((i,) for i in range(1,self.g+1))
        v1 = self.centralizer('v1',selected); v2 = self.centralizer('v2',(indexed(d,e,1),x,xp))
        v3 = self.centralizer('v3',tuple(con(a,v1) for a in base)+tuple(con(a,v2) for a in base))
        v4 = self.centralizer('v4',self.markers())
        self.save(label,tuple(con(a,v3+v4) for a in base))
        self.context['detail'].update(A_star_A=aux,X_B=base,x=x,x_prime=xp); self.end(label,checkpoint)

    def blocks(self,label,source,size,witness,checkpoint):
        self.open(label,'omega',(source,),{'block':size,'zero_block_witness':witness})
        selected = self.cache[source]; old = self.markers(); g0,h,k = old
        keys = ('b','c','t_d','t_d_prime','t_0','t_0_prime','r1','r2')
        fixed = {key:self.declare('D/'+key) for key in keys}; b,c = fixed['b'],fixed['c']
        for key,position in zip(keys[2:6],(1-size,-size,1,0)):
            self.relation('D/'+key+'/b',fixed[key],b,indexed(b,c,position))
            self.relation('D/'+key+'/c',fixed[key],c,repeat(c,2))
        self.fixes('D/r1',fixed['r1'],(indexed(b,c,size),fixed['t_d'],fixed['t_d_prime']))
        self.fixes('D/r2',fixed['r2'],(indexed(b,c,-1),fixed['t_0'],fixed['t_0_prime']))
        fixed_four = tuple(con(x,y) for y in (fixed['r1'],fixed['r2']) for x in (b,c))
        for role,letter in zip(('g0','h','k'),old): self.fixes('D/'+role,letter,fixed_four)
        eleven = tuple(fixed[key] for key in keys)+old; triangle = []
        for n in range(1,size+1):
            row = []; hs = tuple(indexed(h,k,i) for i in range(n))
            sources = (indexed(b,c,n-1),g0)+hs
            for j in range(n):
                targets = (sources[0],con(g0,hs[j]))+tuple(con(hs[i],hs[j]) if i<j else hs[i] for i in range(n))
                row.append(self.maps('D/lambda_'+str(n-1)+'_'+str(j),sources,targets))
            triangle.append(tuple(row))
        ps = [self.centralizer('D/p0',(g0,))]
        for n,row in enumerate(triangle,1):
            anchor = con(g0,indexed(h,k,n-1))+reverse(indexed(b,c,n-1))+reverse(g0)
            ps.append(self.centralizer('D/p'+str(n),(anchor,)+row))
        a = self.centralizer('D/a',tuple(con(x,p) for p in ps for x in eleven)); new = (a,b,c)
        q = self.maps('D/q',new,(a,con(b,repeat(c,size)),c))
        full = eleven+tuple(x for row in triangle for x in row)+tuple(ps)+(a,q)
        q1 = self.centralizer('q1',selected); q2 = self.centralizer('q2',(a,q))
        q3 = self.centralizer('q3',tuple(con(x,q1) for x in full)+tuple(con(x,q2) for x in full))
        q4 = self.centralizer('q4',new); result = tuple(con(x,q3+q4) for x in full)
        self.context['detail'].update(input_role_aliases=dict(zip(('g0','h','k'),old)),X_G=eleven,
                                     lambda_rows=triangle,p_letters=ps,X_D=full,new_marker=new)
        self.carry(old,new); self.save(label,result); self.end(label,checkpoint)

    def final_transfer(self):
        self.open('X_U','two_relator_affine_line_transducer',('Accepted',))
        a,b,c = self.markers(); off=((2,1),(4,1),(6,-1),(8,-1)); vec=((1,-1),(3,1),(5,-1),(7,1))
        alpha = con(a,repeat(b,23)); beta = con(b,c); anchor = con(a,spelling(b,c,off))
        target_word = spelling(self.A['d'],self.A['e'],vec)
        t = self.maps('t',(alpha,beta),(anchor,target_word))
        self.save('X_U',tuple(con(x,t) for x in self.cache['Accepted']))
        self.context['detail'].update(alpha=alpha,beta=beta,target_anchor=anchor,target_direction_word=target_word,
             target_offset=off,target_direction=vec,stable=t,no_marker_cache_A_or_shift_transport=True)
        self.end('X_U',(499,17678,3))


# Independent literal instruction spellings from Pascal's frozen affine table.
# Columns are state, register, positive/next target, optional zero target.
I_ROWS=((1,7,0),(2,6,3),(5,5,6),(7,1,4),(15,4,10),(16,2,20),(19,0,0),
        (20,3,17),(24,2,22),(25,1,26),(27,0,26),(29,6,9),(30,2,0))
D_ROWS=((0,1,1,2),(3,5,2,4),(4,6,5,3),(6,7,7,8),(8,6,29,0),(9,4,0,10),
        (10,5,11,12),(11,5,13,14),(12,2,17,18),(13,5,15,16),(14,3,17,19),
        (17,4,0,21),(18,0,0,17),(22,0,23,25),(23,0,24,28),(26,2,27,22))


def expected_schedule(v):
    v.start()
    v.affine('B0',(),(((1,1),),),'reset2={(0,n)}')
    v.affine('T',((0,1),),(((0,1),(1,1)),),'tau S={(n+1,n)}')
    v.affine('Box1',(),(((0,1),),),'one-supported integer functions')
    v.combine('U0','B0','T',True,(12,27,6))
    v.blocks('V0','U0',2,'B0 contains the zero 2-block',(33,158,19))
    v.moved('V0_shift_minus1','V0',-1); v.combine('W0','V0','V0_shift_minus1',False,(35,196,3))
    v.reflect('N_rho1','W0',(57,653,6)); v.liberate('N_pi1','N_rho1',(69,819,65))
    v.reflect('N_rho2','N_pi1',(91,1644,6)); v.liberate('N_pi2','N_rho2',(103,1878,99))
    v.combine('N','N_pi2','Box1',False,(105,1979,3))
    v.blocks('G_N','N',1,'N contains zero and is one-supported',(123,2079,16))
    directions = tuple(((i,1),(i+9,1)) for i in range(1,9)); edge_names=[]
    groups = [('I',I_ROWS),('Dplus',tuple((q,j,t) for q,j,t,z in D_ROWS)+((28,2,30),)),
              ('Dzero',tuple((q,j,z) for q,j,t,z in D_ROWS))]
    for kind,rows in groups:
        for state,register,target in rows:
            site = register+(10 if kind=='I' else 1)
            offset = ((0,state+1),(9,target+1))
            if kind!='Dzero': offset=tuple(sorted(offset+((site,1),)))
            dirs = directions if kind!='Dzero' else tuple(pair for i,pair in enumerate(directions,1) if i!=site)
            name='edge_'+kind+'_'+str(state)
            detail={'kind':kind,'state':state,'current_tag':state+1,'next_tag':target+1,'changed_or_omitted_coordinate':site}
            v.affine(name,offset,dirs,detail); edge_names.append(name)
    v.affine('Clear',((0,22),),tuple(((i,1),) for i in range(1,9)),'halt-tag to zero block')
    v.affine('Restart',(),tuple(((i,1),) for i in range(9,18)),'zero source, arbitrary next block')
    edge_names+=['Clear','Restart']; prior=edge_names[0]
    demand(len(edge_names)==48 and sum(len(v.cache[x]) for x in edge_names)==417,'48 literal affine leaves')
    for i,right in enumerate(edge_names[1:],1):
        label='R_bare' if i==47 else 'Run_union_'+str(i)
        v.combine(label,prior,right,True,(217,2772,6) if i==47 else None); prior=label
    v.blocks('Omega','R_bare',18,'Restart contains the zero 18-block',(422,6071,203))
    v.moved('Omega_shift_minus9','Omega',-9); v.combine('H_bare','Omega','Omega_shift_minus9',False,(424,6477,3))
    v.combine('Hist_aff','H_bare','G_N',False,(426,6496,3))
    v.reflect('Block_rho1','Hist_aff',(448,10472,6)); v.liberate('Block_pi1','Block_rho1',(460,11420,456))
    v.reflect('Block_rho2','Block_pi1',(482,16155,6)); v.moved('Block_shift_minus8','Block_rho2',-8)
    v.liberate('Block_pi2','Block_shift_minus8',(494,17171,490)); v.moved('Block_shift_plus8','Block_pi2',8)
    v.affine('Box9',(),tuple(((i,1),) for i in range(9)),'arbitrary nine-block')
    v.affine('Init',((0,23),),(((1,1),),),'tag23, arbitrary input at site1')
    v.combine('Reach_aff','Block_shift_plus8','Box9',False,(496,17671,3))
    v.combine('Accepted','Reach_aff','Init',False,(498,17676,3)); v.final_transfer()
    demand(edge_names==v.data['affine_edge_order'],'entire edge order')


def audit():
    for filename,pin in PINS.items():
        raw=(TMP/filename).read_bytes(); actual=hashlib.sha256(raw).hexdigest()
        demand(actual==pin,'byte binding '+filename)
        REPORT['bindings'].append({'path':str(TMP/filename),'sha256':pin,'bytes':len(raw)})
    raw=(TMP/'positive7_higman_literal_presentation_riemann.json').read_bytes(); data=json.loads(raw)
    expected_keys={'schema','scope','excluded','source','dependencies','word_conventions','generators','relators',
                   'trace','affine_edge_order','final_state','cached_lists','selected_list_name','selected_list',
                   'census','status','retained_boundaries'}
    demand(set(data)==expected_keys,'complete top-level schema')
    demand(data['schema']=='positive7-preembedding-literal-presentation-v1','schema')
    source_path=TMP/'positive7_higman_literal_presentation_riemann.py'; source_bytes=source_path.read_bytes()
    demand(data['source']=={'path_at_first_run':str(source_path),'sha256':PINS[source_path.name],
                           'bytes':len(source_bytes),'LF_lines':source_bytes.count(b'\n')},'author source identity')
    proof_blobs=[('positive7_higman_benign_recipes_aristotle.md','4bae002fb8879093192b956c6f57755b7a93898f'),
                 ('positive7_higman_shared_ambient_aristotle.md','73f3f9c0bf31f7a60124e317140bac09d2b7b571'),
                 ('positive7_higman_shared_schedule_riemann.md','d48ae47879f116bdf58180c77da0dd3f88ed603a'),
                 ('positive7_affine_typed_recognizer_pascal.md','a30a70cea179b6194b5facdf50353fc4067d49c9'),
                 ('positive7_higman_affine_line_transducer_aristotle.md','22732da84a880ec83a3de3d26c6c3d9a853b4829')]
    expected_dependencies=[]
    for name,blob in proof_blobs:
        b=(TMP/name).read_bytes()
        expected_dependencies.append({'path':'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'+name,
            'commit':'81315a6b3a408880fdd04bc5754cf69991c0ba40','git_blob':blob,'sha256':PINS[name],
            'bytes':len(b),'LF_lines':b.count(b'\n')})
    demand(data['dependencies']==expected_dependencies,'complete immutable dependency declarations')
    conventions={'letters':'nonzero signed sequential generator IDs','empty_word':[],
                 'conjugation':'inverse(by) + word + by','relator':'inverse(stable) + source + stable + inverse(target)',
                 'simplification':'none, including adjacent inverse letters',
                 'input_renaming':'old IDs retained as explicitly traced role aliases',
                 'affine_basis':'all nine tracked initial-A images retained literally after transport',
                 'final_target':'anchor uses current markers; direction uses tracked initial-A d/e'}
    demand(data['word_conventions']==conventions,'complete lexical convention metadata')
    demand(data['scope']=='Literal syntax only; imported subgroup-identification premises remain attributed.','scope')
    demand(data['excluded']==['group reduction or word-problem evaluation','machine execution','Mikaelian Section 7 embedding',
                             'matrix alphabet','Diophantine arithmetic bound'],'excluded scope')
    demand(data['status']=='first original literal-string emission; independent audit separate','first status')
    demand(data['retained_boundaries']==[
        'Every fresh omega letter remains distinct even when its displayed action duplicates another.',
        'The new wrapper output is excluded from persistent transport of old caches.',
        'The final two-relator stable letter does not normalize the marker F.',
        'The downstream Section 7.4 noninjective map blocks the historical conditional 20808 route; no such embedding is emitted.'],
        'all retained source boundaries')
    checker=Comparator(data); expected_schedule(checker)
    demand((checker.g,checker.r,checker.event)==(499,17678,124),'complete record counts')
    demand(len(data['generators'])==499 and len(data['relators'])==17678 and len(data['trace'])==124,'no extra records')
    demand(checker.used==set(range(1,500)),'every declared generator occurs in literal relators')
    demand(normal(checker.state())==data['final_state'],'entire final state')
    demand(normal(checker.cache)==data['cached_lists'],'all final cache words')
    demand(data['selected_list_name']=='X_U' and normal(checker.cache['X_U'])==data['selected_list'],'final output')
    counts={'generators':499,'relators':17678,'selected_words':3,'cached_lists':len(checker.cache),'events':124,
            'relator_letters':checker.letters,'cached_word_letters':sum(len(w) for words in checker.cache.values() for w in words)}
    demand(counts==data['census'],'literal length census')
    demand(counts['cached_lists']==123 and counts['relator_letters']==1247773 and counts['cached_word_letters']==542771,'first-emission measured lengths')
    REPORT.update(status='PASS:499 generators,17678 literal relators,124 traces,123 caches,3 final words',
                  census=counts,events=checker.event_summaries,
                  generators_sha256=digest(data['generators']),relators_sha256=digest(data['relators']),
                  trace_sha256=digest(data['trace']),cached_lists_sha256=digest(data['cached_lists']),
                  selected_list_sha256=digest(data['selected_list']),
                  boundaries=['No free-group reduction or word-problem evaluation.',
                              'Only preembedding benign pair; Section7 embedding and20808 are not validated.',
                              'Imported operation-specific subgroup-identification premises remain attributed.'])


try:
    audit()
except Exception:
    REPORT['status']='FAIL: first result retained permanently'
    REPORT['error']=traceback.format_exc()
    OUT.write_text(json.dumps(REPORT,indent=2)+'\n')
    raise
else:
    OUT.write_text(json.dumps(REPORT,indent=2)+'\n')
    print(REPORT['status'])
