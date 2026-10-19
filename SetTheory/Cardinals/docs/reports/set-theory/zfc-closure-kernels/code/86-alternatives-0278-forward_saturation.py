#!/usr/bin/env python3
"""Exact finite-algorithm C254 forward search; no proof-certificate input.
Generates native-Cantor records, keeps proved flags, and fairly re-sweeps.
This is NOT an emitted binary Turing machine or a state-count claim.
"""
from pathlib import Path
import sys,json,itertools,copy
if not __debug__:raise RuntimeError('Run without -O.')
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'architectures'))
import pattern_oracle as O
import canonical_arena as A
C,P,T=O.load_source();ORACLE=O.compile_oracle(T)

def representative_paths(t):
    found={}
    def visit(x,path):
        if x[0]=='p':
            i=x[1]
            if i not in found or (len(path),path)<(len(found[i]),found[i]):found[i]=path
        elif x[0]!='z':visit(x[1],path+[0]);visit(x[2],path+[1])
    visit(t,[]);return found

REPS={rule:representative_paths(root) for rule,root in ORACLE['syntax'].items()}
assert all(set(REPS[rule])==set(range(t.arity)) for rule,t in T.items())
assert all(root[0]==0 for root in ORACLE['syntax'].values())

def follow(nodes,root,path):
    for bit in path:
        root=0 if root==0 else nodes[root][2+bit]
    return root

def infer_arguments(nodes,root,rule):
    return [follow(nodes,root,REPS[rule][j]) for j in range(T[rule].arity)]

def recognize(nodes,root,rule):
    """None, or the unique parameter tuple for this exact template instance.
    Prerequisite: validated canonical arena. No guesses are accepted as input.
    """
    args=infer_arguments(nodes,root,rule)
    if rule==11 and (args[2]==args[0] or args[2]==args[1]):return None
    return args if O.match_oracle(nodes,root,args,ORACLE,rule) else None

def recognize_by_markers(nodes,root,rule):
    """Five finite leaf-class passes, one mutable temporary node marker.
    Root identity is preserved independently. No parameter tuple is stored.
    The extra bundle pass reads but does not change the last (P2) marker.
    """
    marker=[False]*len(nodes)
    for leafclass in (0,1,2,4,3):  # Z, P0, P1, P3, P2; P2 deliberately last.
        marker[:]=[False]*len(nodes)
        bound=leafclass==0
        if bound:marker[0]=True
        for path,expected,leaf in O.enumerate_leaf_paths(ORACLE,rule):
            actual=root;observed=[]
            for bit in path:
                tag,left,right=(0,0,0) if actual==0 else nodes[actual][1:]
                observed.append((tag>>bit)&1);actual=(left,right)[bit]
            if observed!=expected:return False
            if leaf!=leafclass:continue
            if not bound:marker[actual]=True;bound=True
            elif not marker[actual]:return False
    if rule==11:
        assert any(marker)  # Every current bundle template uses parameter2.
        for path,expected,leaf in O.enumerate_leaf_paths(ORACLE,rule):
            if leaf in (1,2) and marker[follow(nodes,root,path)]:return False
    return True

def native_records():
    """Record ID equals native numeral. Zero is the virtual Imp(0,0)."""
    yield ['z']
    for m in itertools.count():
        for right in range(m+1):
            left=m-right
            for tag in range(4):
                if (tag,left,right)!=(0,0,0):yield ['b',tag,left,right]

class Search:
    def __init__(self,*,audit=False,recognizer='marker'):
        self.generator=native_records();self.nodes=[next(self.generator)]
        self.proved=[True];self.halted=False;self.sweeps=0
        self.audit=audit;self.recognizer=recognizer
        if recognizer not in ('marker','representatives'):raise ValueError('recognizer')
        # Audit witnesses are optional diagnostics, not machine input/state.
        self.rows=[dict(tag=0,args=[],children=[],formula=0)] if audit else None
        self.row_of={0:0} if audit else None
    def mark(self,n,tag,args,children):
        if not self.proved[n]:
            self.proved[n]=True
            if self.audit:
                self.row_of[n]=len(self.rows)
                self.rows.append(dict(tag=tag,args=args,children=[self.row_of[c] for c in children],formula=n))
        if n==1:self.halted=True
    def sweep(self):
        if self.halted:return
        for n,node in enumerate(self.nodes):
            tag,left,right=(0,0,0) if n==0 else node[1:]
            if tag==0:
                if not self.proved[n]:
                    for rule in T:
                        if self.recognizer=='marker':
                            matched=recognize_by_markers(self.nodes,n,rule)
                            args=infer_arguments(self.nodes,n,rule) if matched and self.audit else []
                        else:
                            args=recognize(self.nodes,n,rule);matched=args is not None
                        if matched:
                            self.mark(n,rule,args,[]);break
                if self.proved[n] and self.proved[left]:
                    self.mark(right,1,[right],[left,n])
            elif tag==2 and self.proved[right]:
                self.mark(n,2,[left],[right])
            if self.halted:break
        self.sweeps+=1
    def advance(self):
        """One finite sweep, then one new native record unless F was found."""
        self.sweep()
        if not self.halted:
            record=next(self.generator);i=len(self.nodes)
            _,tag,left,right=record
            assert left<i and right<i and (tag,left,right)!=(0,0,0)
            self.nodes.append(record);self.proved.append(False)
    def semidecide(self):
        while not self.halted:self.advance()
    def certificate(self):
        if not self.audit:raise ValueError('audit not enabled')
        return dict(format=A.FORMAT,nodes=copy.deepcopy(self.nodes),proof_rows=copy.deepcopy(self.rows))

def tests():
    counts={'template_generated_instances':0,'inferred_parameter_equalities':0,
      'canonical_root_template_checks':0,'finite_sweeps':0,'audit_soundness_certificates':0,
      'zero_path_checks':0,'sparse_repeated_mp_sweeps':0,'marker_recognizer_equivalences':0}
    # Sparse canonical arenas test every template deeply without building an
    # astronomically long prefix up to a full set-theory-bundle code.
    for rule,t in T.items():
        for args in itertools.product(range(3),repeat=t.arity):
            nodes=O.canonical_start_arena();intern={tuple(n[1:]):i for i,n in enumerate(nodes) if i}
            root=O.make_instance(ORACLE['syntax'][rule],args,nodes,intern)
            inferred=infer_arguments(nodes,root,rule)
            assert inferred==list(args)
            allowed=rule!=11 or (args[2]!=args[0] and args[2]!=args[1])
            assert recognize(nodes,root,rule)==(list(args) if allowed else None)
            assert recognize_by_markers(nodes,root,rule)==allowed
            counts['marker_recognizer_equivalences']+=1
            counts['template_generated_instances']+=1;counts['inferred_parameter_equalities']+=t.arity
    nodes=A.generated_prefix(255,pairing='cantor')
    for root in range(len(nodes)):
        for rule in T:
            args=infer_arguments(nodes,root,rule)
            expected=O.match_oracle(nodes,root,args,ORACLE,rule)
            if rule==11:expected=expected and args[2]!=args[0] and args[2]!=args[1]
            assert (recognize(nodes,root,rule) is not None)==expected
            assert recognize_by_markers(nodes,root,rule)==expected
            counts['marker_recognizer_equivalences']+=1
            counts['canonical_root_template_checks']+=1
    for pathlen in range(32):
        assert follow([['z']],0,[1]*pathlen)==0;counts['zero_path_checks']+=1
    # Explicit alias: the all-zero propositional row is code0 and recognized.
    assert recognize([['z']],0,10)==[0,0,0,0]
    # Fixed-F can never be an AX output, even before a proof search runs.
    assert all(recognize(nodes,1,rule) is None for rule in T)
    search=Search(audit=True)
    for _ in range(129):
        before=search.proved.copy();search.advance();counts['finite_sweeps']+=1
        assert not search.halted
        assert all(not flag or search.proved[i] for i,flag in enumerate(before))
        assert A.native_values(search.nodes)==list(range(len(search.nodes)))
        cert=search.certificate();goal=cert['proof_rows'][-1]['formula']
        assert A.verify(cert,control_goal=goal)
        assert not A.verify(cert)
        counts['audit_soundness_certificates']+=1
    assert search.proved[0] and search.proved[2] and search.proved[6] and not search.proved[1]
    # A full positive propositional axiom and two delayed MP firings. The
    # sparse arena avoids enumerating 261,361 native records for this control.
    # This diagnostic uses only sweep(), whose invariant works for any
    # canonical arena with fixed F at ID1; production uses native_records().
    sparse=O.canonical_start_arena();intern={tuple(n[1:]):i for i,n in enumerate(sparse) if i}
    major=O.make_instance(ORACLE['syntax'][10],[0,2,0,0],sparse,intern)
    target=sparse[major][3];target2=sparse[target][3]
    probe=Search(audit=True);probe.nodes=sparse;probe.proved=[i==0 for i in range(len(sparse))]
    for _ in range(3):
        probe.sweep();cert=probe.certificate();goal=cert['proof_rows'][-1]['formula']
        assert A.verify(cert,control_goal=goal) and not A.verify(cert)
        counts['sparse_repeated_mp_sweeps']+=1
    assert probe.proved[major] and probe.proved[target] and probe.proved[target2]
    assert len([row for row in probe.rows if row['tag']==1])>=2
    return dict(counts,marked_native_codes=[i for i,b in enumerate(search.proved) if b],
      representative_paths=REPS,all_passed=True,
      scope='Finite exact reference diagnostics. General search theorem in forward_saturation.md. No binary machine or state-count claim.')
if __name__=='__main__':
    result=tests();(HERE/'forward_saturation_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
