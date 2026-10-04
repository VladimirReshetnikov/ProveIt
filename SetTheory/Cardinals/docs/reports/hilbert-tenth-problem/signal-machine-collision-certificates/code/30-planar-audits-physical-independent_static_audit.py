"""Independent rational specification audit. Never imports/executes packet code.

Inputs are inert JSON. Rebuilds algebra, endpoint inequalities and a prescribed
symbolic word grammar. Does not select collisions or advance physical particles.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math
import stat

SRC = Path('/workspace/shared/five-signal-planar-realization60-20261004')
OUT = Path(__file__).resolve().parent
Z = (Q(0), Q(0), Q(0))
D0 = (Q(1), Q(0), Q(0))
I = ((Q(1), Q(0)), (Q(0), Q(1)))

def require(test, message):
    if not test:
        raise RuntimeError(message)

def vec(*entries):
    return tuple(map(Q, entries))

def lin(*terms):
    return tuple(sum(coef * row[j] for coef, row in terms) for j in range(3))

def prod(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)) for i in range(2))

def det(A):
    return A[0][0]*A[1][1] - A[0][1]*A[1][0]

def smatrix(axis, t):
    return ((Q(1), t), (Q(0), Q(1))) if axis == 'x' else ((Q(1), Q(0)), (t, Q(1)))

def specifications(A):
    q = det(A)
    require(q > 0, 'matrix determinant')
    B = ((A[0][0]/q, A[0][1]/q), A[1])
    a,b = B[0]; c,d = B[1]
    require(det(B)==1, 'normalized determinant')
    if c != 0:
        branch = 'nonzero_c'
        shears = [('x',(d-1)/c), ('y',c), ('x',(a-1)/c)]
    elif b != 0:
        branch = 'upper_triangular'
        shears = [('y',(a-1)/b), ('x',b), ('y',(d-1)/b)]
    else:
        branch = 'diagonal'
        shears = [('y',-a), ('x',1/a-1), ('y',Q(1)), ('x',a-1)]
    reconstructed = I
    for axis,t in shears:
        reconstructed = prod(smatrix(axis,t),reconstructed)
    require(reconstructed == B, 'chronological SL2 reconstruction')
    H = 0 if q == 1 else max(1, math.ceil(4*abs(q-1)/min(Q(1),q)))
    u = [1+Q(j,H)*(q-1) for j in range(H+1)] if H else [Q(1)]
    dilation = [u[j]/u[j-1] for j in range(1,H+1)]
    cumulative = Q(1)
    for f in dilation:
        require(Q(3,4) <= f <= Q(5,4), 'small factor interval')
        cumulative *= f
    require(cumulative == q, 'rational factor telescope')
    require(prod(((q,Q(0)),(Q(0),Q(1))),reconstructed)==A, 'general product orientation')
    return branch,shears,dilation

class Specification:
    def __init__(self):
        self.p = {'L':Z,'X':vec('1/3',1,0),'Y':vec('2/3',0,1),'D':D0}
        self.anchor='L'
        self.direction=1
        self.duration=Z
        self.guards=[]
        self.phases=[]
        self.events=[]
        self.speeds={s+'0':Q(0) for s in self.p}
        self.labels={s:s+'0' for s in self.p}
        self.temporary=0
        self.K=self.T=self.H=self.B=0
    def distance(self, marker):
        return self.p[marker] if self.anchor=='L' else lin((1,self.p['D']),(-1,self.p[marker]))
    def store_distance(self, marker, row):
        self.p[marker] = row if self.anchor=='L' else lin((1,self.p['D']),(-1,row))
    def emit_tokens(self,tokens):
        for marker,direction,replacement in tokens:
            n=len(self.events)
            before=self.labels[marker]
            after=before if replacement is None else replacement
            self.events.append({'index':n,'marker':marker,'marker_in':before,'marker_out':after,
              'messenger_in_speed':Q(self.direction),'messenger_out_speed':Q(direction)})
            self.labels[marker]=after
            self.direction=direction
    def temporary_label(self,speed):
        label='T'+str(self.temporary)
        self.temporary+=1
        self.speeds[label]=speed
        return label
    def move_anchor(self,anchor):
        if anchor==self.anchor:
            return
        direction=1 if self.anchor=='L' else -1
        require(self.direction==direction,'transfer entrance phase')
        order=['X','Y'] if direction==1 else ['Y','X']
        start=len(self.events)
        self.emit_tokens([(s,direction,None) for s in order]+[(anchor,-direction,None)])
        self.phases.append({'kind':'transfer','anchor':anchor,'start':start,'stop':len(self.events)})
        self.duration=lin((1,self.duration),(1,self.p['D']))
        self.anchor=anchor
        self.T+=1
    def primitive(self,kind,target,parameter,reflector=None,spectators=()):
        s=1 if self.anchor=='L' else -1
        require(self.direction==s,'primitive entrance phase')
        old=self.distance(target)
        start=len(self.events)
        if kind=='L':
            endpoint=lin((parameter,old))
            speed=s*(parameter-1)/(parameter+1)
            temporary=self.temporary_label(speed)
            forward=[(a,s,None) for a in spectators]
            backward=[(a,-s,None) for a in reversed(spectators)]
            tokens=forward+[(target,-s,temporary)]+backward+[(self.anchor,s,None)]
            tokens+=forward+[(target,-s,target+'0')]+backward+[(self.anchor,s,None)]
            duration=lin((2,old),(2,endpoint))
            extra={'inner_spectators':list(spectators)}
        else:
            require(kind=='H','primitive type')
            ref=self.distance(reflector)
            endpoint=lin((parameter,old),(1-parameter,ref))
            temporary=self.temporary_label(s*(1-parameter)/(1+parameter))
            tokens=[(target,s,temporary)]+[(a,s,None) for a in spectators]
            tokens += [(reflector,-s,None)]+[(a,-s,None) for a in reversed(spectators)]
            tokens += [(target,-s,target+'0'),(self.anchor,s,None)]
            duration=lin((2,ref))
            extra={'reflector':reflector,'spectators':list(spectators)}
        require(parameter>0,'positive primitive parameter')
        self.emit_tokens(tokens)
        self.phases.append({'kind':kind,'target':target,'anchor':self.anchor,'parameter':parameter,
          'start':start,'stop':len(self.events),'from':old,'to':endpoint,**extra})
        self.store_distance(target,endpoint)
        self.duration=lin((1,self.duration),(1,duration))
    def translation(self,target,reflector,e,spectators=()):
        require(e<1,'translation parameter')
        before=self.distance(target)
        ref=self.distance(reflector)
        self.primitive('L',target,1/(1-e))
        self.primitive('H',target,1-e,reflector,spectators)
        require(self.distance(target)==lin((1,before),(e,ref)),'translation algebra')
    def add_guard(self,name,row):
        self.guards.append({'name':name,'row':row})
    def endpoints(self,name,target,neighbor):
        self.add_guard(name+':lower',target)
        self.add_guard(name+':upper',lin((1,neighbor),(-1,target)))
    def shear(self,axis,t):
        self.B+=1
        name='block'+str(self.B)
        self.move_anchor('L' if axis=='x' else 'D')
        target,near,far=('X','Y','D') if axis=='x' else ('Y','X','L')
        N=max(1,math.ceil(4*abs(t))); delta=t/N; self.K+=N
        neighbor=self.distance(near)
        self.add_guard(name+':neighbor_lower',neighbor)
        self.add_guard(name+':neighbor_upper',lin((1,self.p['D']),(-1,neighbor)))
        self.endpoints(name+':0',self.distance(target),neighbor)
        for k in range(N):
            self.translation(target,near,delta)
            self.endpoints(name+':'+str(2*k+1),self.distance(target),neighbor)
            self.translation(target,far,-Q(2,3)*delta,(near,))
            self.endpoints(name+':'+str(2*k+2),self.distance(target),neighbor)
    def dilation(self,q):
        self.move_anchor('L'); self.H+=1
        name='dilation'+str(self.H); y=self.p['Y']
        self.add_guard(name+':neighbor_lower',y)
        self.add_guard(name+':neighbor_upper',lin((1,self.p['D']),(-1,y)))
        self.endpoints(name+':start',self.p['X'],y)
        self.primitive('L','X',q)
        self.endpoints(name+':scaled',self.p['X'],y)
        self.translation('X','D',(1-q)/3,('Y',))
        self.endpoints(name+':end',self.p['X'],y)
    def export(self,A,lam,shears,dilations):
        self.move_anchor('L')
        suffix=int(lam!=1)
        if suffix:
            order=['X','Y','D'] if lam<1 else ['D','Y','X']
            for target in order:
                inner={'X':(),'Y':('X',),'D':('X','Y')}[target]
                self.primitive('L',target,lam,spectators=inner)
        m=len(self.events)
        for n,event in enumerate(self.events):
            self.speeds['Q'+str(n)]=event['messenger_in_speed']
            event['input']=['Q'+str(n),event['marker_in']]
            event['output']=['Q'+str((n+1)%m),event['marker_out']]
        require(self.direction==1 and self.anchor=='L','anchor wrap closure')
        require(self.labels=={s:s+'0' for s in self.p},'marker label restoration')
        expected={'L':Z,'D':vec(lam,0,0),'X':vec(lam/3,lam*A[0][0],lam*A[0][1]),'Y':vec(2*lam/3,lam*A[1][0],lam*A[1][1])}
        require(self.p==expected,'final homogeneous rows')
        counts={'shear_blocks':self.B,'micro_shears':self.K,'anchor_transfers':self.T,
        'centered_dilation_steps':self.H,'events':18*self.K+3*self.T+14*self.H+24*suffix,
        'supplied_guards':4*self.K+4*self.B+8*self.H,'temporary_labels':4*self.K+3*self.H+3*suffix,
        'meta_signals':22*self.K+3*self.T+17*self.H+27*suffix+4,'live_signals':5}
        require(m==counts['events'] and len(self.guards)==counts['supplied_guards'],'word/guard sizes')
        require(self.temporary==counts['temporary_labels'] and len(self.speeds)==counts['meta_signals'],'alphabet counts')
        require(all(g['row'][0]>0 for g in self.guards),'center strictness')
        for n,event in enumerate(self.events):
            require(event['messenger_out_speed']==self.speeds['Q'+str((n+1)%m)],'phase speed wrap')
            for key in ['input','output']:
                aa,bb=event[key]
                require(self.speeds[aa]!=self.speeds[bb],'pairwise distinct speeds')
        return {'matrix':A,'lambda':lam,'chronological_shears':shears,'centered_x_factors':dilations,
        'counts':counts,'return_marker_rows':self.p,'duration_row':self.duration,'guard_rows':self.guards,
        'primitive_phases':self.phases,'speeds':self.speeds,'binary_word':self.events,
        'completion':'Identity on every other collision input set with pairwise distinct speeds.'}

def serialize(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serialize(y) for y in x]
    return x

def polygon(rows):
    # Initial-order triangle in centered (X,Y); independently supplied rows
    # include this triangle, so clipping loses no portion of the true chamber.
    vertices=[(Q(-1,3),Q(-2,3)),(Q(-1,3),Q(1,3)),(Q(2,3),Q(1,3))]
    for a,b,c in rows:
        result=[]
        for i,P in enumerate(vertices):
            R=vertices[(i+1)%len(vertices)]
            f=a+b*P[0]+c*P[1]; g=a+b*R[0]+c*R[1]
            if f>=0: result.append(P)
            if (f<0<g) or (g<0<f):
                ratio=f/(f-g)
                result.append((P[0]+ratio*(R[0]-P[0]),P[1]+ratio*(R[1]-P[1])))
        vertices=[]
        for p in result:
            if not vertices or p!=vertices[-1]: vertices.append(p)
        if len(vertices)>1 and vertices[0]==vertices[-1]: vertices.pop()
        require(len(vertices)>=3,'nonempty full-dimensional closed chamber')
    require(all(a+b*x+c*y>=0 for x,y in vertices for a,b,c in rows),'polygon feasibility')
    area=abs(sum(vertices[i][0]*vertices[(i+1)%len(vertices)][1]-vertices[i][1]*vertices[(i+1)%len(vertices)][0] for i in range(len(vertices))))/2
    require(area>0,'positive chamber area')
    return vertices,area

def audit_files():
    reports=[]
    for file in sorted((SRC/'evidence').glob('*.json')):
        if file.name=='summary.json': continue
        original=json.loads(file.read_text())
        A=tuple(tuple(map(Q,row)) for row in original['matrix']); lam=Q(original['lambda'])
        branch,shears,dilations=specifications(A)
        independent=Specification()
        for axis,t in shears: independent.shear(axis,t)
        independent.move_anchor('L')
        for q in dilations: independent.dilation(q)
        expected=independent.export(A,lam,shears,dilations)
        require(serialize(expected)==original,'full independent reconstruction mismatch: '+file.name)
        vertices,area=polygon([g['row'] for g in expected['guard_rows']])
        eps=int(lam!=1); K=independent.K; H=independent.H; T=independent.T
        cap=12*K+T+10*H+6*(1+lam)*eps
        duration=expected['duration_row']; dc=duration[0]
        require(2<=dc<cap,'center time bounds')
        require(all(2<=duration[0]+duration[1]*x+duration[2]*y<=cap for x,y in vertices),'closed-polygon duration bounds')
        reports.append({'file':file.name,'source_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
          'branch':branch,'determinant':str(det(A)),'lambda':str(lam),'counts':expected['counts'],
          'center_duration':str(dc),'closed_chamber_vertices':serialize(vertices),'closed_chamber_area':str(area),
          'full_json_reconstruction':'identical','polygon_and_duration':'passed'})
    return reports

def algebra_sweep():
    n=0; branches=set(); dets=set()
    for a in range(-3,4):
      for b in range(-3,4):
       for c in range(-3,4):
        for d in range(-3,4):
         A=((Q(a),Q(b)),(Q(c),Q(d)))
         if det(A)>0:
          branch,ss,qs=specifications(A); n+=1; branches.add(branch); dets.add(str(det(A)))
    # Deliberately include near-one endpoints, below-one telescopes, and awkward denominators.
    factors=[Q(1),Q(3,4),Q(5,4),Q(1,17),Q(17,16),Q(16,17),Q(101,97),Q(97,101)]
    for q in factors:
        specifications(((q,Q(0)),(Q(0),Q(1))))
    # Concrete necessity witness for retaining the intermediate q*x endpoint.
    q,x,y=Q(5,4),Q(1,2),Q(3,5)
    end=q*x+(1-q)/3
    require(0<x<y<1 and 0<end<y and q*x>y,'dilation internal-endpoint witness')
    return {'integer_matrices_checked':n,'entry_range':'all integers from -3 through 3',
      'branches':sorted(branches),'positive_determinants':sorted(dets,key=Q),
      'extra_centered_factors':serialize(factors),
      'intermediate_guard_necessity_witness':serialize({'q':q,'x':x,'y':y,'qx':q*x,'final_x':end})}

def main():
    before=json.loads((OUT/'frozen_inventory_before.json').read_text())
    reports=audit_files()
    sweep=algebra_sweep()
    after=[]
    for x in sorted(SRC.rglob('*')):
        s=x.stat(); after.append({'path':str(x.relative_to(SRC)),'mode':stat.S_IMODE(s.st_mode),
        'mtime_ns':s.st_mtime_ns,'size':s.st_size,'is_file':x.is_file(),
        **({'sha256':hashlib.sha256(x.read_bytes()).hexdigest()} if x.is_file() else {})})
    require(after==before,'frozen bytes/modes/mtimes changed')
    output={'status':'PASS','fixtures':len(reports),'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'source_proof_sha256':hashlib.sha256((SRC/'PROOF.md').read_bytes()).hexdigest(),
      'source_manifest_sha256':hashlib.sha256((SRC/'PACKET_MANIFEST.json').read_bytes()).hexdigest(),
      'frozen_bytes_modes_mtimes':'unchanged','no_author_code_executed':True,'no_physical_simulation':True,
      'algebra_sweep':sweep,'results':reports}
    (OUT/'independent_results.json').write_text(json.dumps(output,indent=2)+'\n')
    (OUT/'frozen_inventory_after.json').write_text(json.dumps(after,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='results'},indent=2))

if __name__=='__main__': main()
