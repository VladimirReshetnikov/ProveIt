#!/usr/bin/env python3
"""Independent text/header/metric assertions. No Lean execution."""
import re,unittest
from pathlib import Path
from static_audit import mask_noncode
BASE=Path(__file__).resolve().parents[1]
SRC=BASE/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'

def declaration(text,name):
    start=re.search(r'^(?:@\[[^\n]*\]\s+)?(?:theorem|def) '+re.escape(name)+r'\b',text,re.M)
    if not start:raise ValueError(name)
    rest=text[start.start():]
    end=re.search(r'\n(?:@\[[^\n]*\]\s+)?(?:theorem|def|end)\b',rest)
    return rest[:end.start() if end else len(rest)]
def nonblank(text):return sum(bool(l.strip()) for l in mask_noncode(text).splitlines())
def header(text):return text.split(':=',1)[0]

class SourceContractTests(unittest.TestCase):
    def test_machine_exact_headers_and_independent_metrics(self):
        cases=[('WangMachineAction','act_next_none_iff',10,3,8,1),('WangMachineStep','color_action',15,11,8,4),('WangMachineTraceBounds','run_read_of_abs_ge',8,3,6,1)]
        for module,name,old,new,ob,nb in cases:
            a=declaration((SRC/(module+'.lean')).read_text(),name);b=declaration((BASE/'machine/patched/Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(module+'.lean')).read_text(),name)
            self.assertEqual(header(a),header(b));self.assertEqual((nonblank(a),nonblank(b)),(old,new))
            self.assertEqual((nonblank(a.split(':= by',1)[1]),nonblank(b.split(':= by',1)[1])),(ob,nb))
    def test_encoding_header_exact_mapping_and_import_cost(self):
        a=(SRC/'WangMachineEncoding.lean').read_text();b=(BASE/'encoding/WangMachineEncodingCandidate.lean').read_text()
        oa=declaration(a,'stateNumber_injective');nb=declaration(b,'stateNumber_injective')
        self.assertEqual(header(oa),header(nb));self.assertEqual((nonblank(oa),nonblank(nb)),(18,7))
        self.assertEqual(declaration(a,'stateNumber'),declaration(b,'stateNumber'))
        self.assertEqual(len(re.findall(r'^import ',b,re.M))-len(re.findall(r'^import ',a,re.M)),1)
        self.assertIn('finSuccEquivLast.symm',nb);self.assertNotRegex(nb,r'\bfinSuccEquiv\b')
    def test_interval_exact_header_and_metrics(self):
        a=declaration((SRC/'WangTiles942ResetRows.lean').read_text(),'interval_propagate');b=declaration((BASE/'rows/proposed/WangTiles942ResetRows.lean').read_text(),'interval_propagate')
        self.assertEqual(header(a),header(b));self.assertEqual((nonblank(a),nonblank(b)),(31,23))
        self.assertEqual((nonblank(a.split(':= by',1)[1]),nonblank(b.split(':= by',1)[1])),(26,18))
    def test_bond_definitions_unchanged_and_api_change_explicit(self):
        a=(SRC/'WangTiles942StepConstruction.lean').read_text();b=(BASE/'rows/proposed/WangTiles942StepConstruction.lean').read_text()
        for name in ['sourceIndex','nextHead','receiveTile','stepTile']:
            self.assertEqual(declaration(a,name),declaration(b,name))
        for name in ['stepTile_west','stepTile_east']:
            self.assertNotEqual(header(declaration(a,name)),header(declaration(b,name)))
        for name in ['stepTile_horizontal','step_row']:
            self.assertEqual(header(declaration(a,name)),header(declaration(b,name)))
        def block(s,start):return s[s.index(start):s.index('theorem step_row')]
        self.assertEqual((nonblank(block(a,'theorem stepTile_west')),nonblank(block(b,'def bondSignal'))),(28,29))
    def test_probes_do_not_call_original_replaced_theorems(self):
        selected=[('machine/MachineCandidates.lean',['act_next_none_iff','color_action','run_read_of_abs_ge']),('encoding/StateNumberCandidate.lean',['stateNumber_injective']),('rows/BondPulseCandidate.lean',['stepTile_west','stepTile_east','stepTile_horizontal']),('rows/IntervalPropagationCandidate.lean',['interval_propagate'])]
        for path,names in selected:
            code=mask_noncode((BASE/path).read_text())
            for name in names:self.assertNotRegex(code,r'\b'+name+r'\b')
    def test_all_candidate_audits_after_namespace_end(self):
        for path in ['machine/MachineCandidates.lean','encoding/StateNumberCandidate.lean','rows/BondPulseCandidate.lean','rows/IntervalPropagationCandidate.lean']:
            s=(BASE/path).read_text();self.assertGreater(s.index('#print axioms'),s.rindex('\nend '))
if __name__=='__main__':unittest.main()
