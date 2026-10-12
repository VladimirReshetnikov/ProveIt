"""Native source authentication for opt-in signed annulus certificates."""

from copy import deepcopy
import json
from pathlib import Path
import unittest

from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


def native_case(name):
    path = Path(__file__).resolve().parents[1] / 'marked_parallelity_research/corpus.json'
    return next(c for c in json.loads(path.read_text())['cases'] if c['id'] == name)


class SignedAnnulusIntegrationTests(unittest.TestCase):
    def test_opt_in_preserves_native_complete_censuses(self):
        for name in ('pilot/fibonacci_lst_05/0', 'fibonacci_lst_05/mixed',
                     'lst_1_1/mixed'):
            c = native_case(name)
            old = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                          boundary_method='moments')
            new = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                          boundary_method='moments',
                                          annulus_method='signed_rank_two',
                                          record_certificate=True)
            self.assertEqual(new['status'], 'COMPLETE')
            self.assertEqual(new['census'], old['census'])
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],
                                                           c['coordinates'],
                                                           new['certificate']))

    def test_native_signed_envelope_and_replay(self):
        # This genuine normal surface was in report 57's discovery bank, but
        # not the small marked-parallelity corpus.  It has a complete raw core
        # and a simultaneous primitive annular family missed by raw counts.
        path = Path(__file__).resolve().parents[1] / 'signed_annulus_research/corpus.json'
        c = json.loads(path.read_text())['cases'][0]
        baseline = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                           boundary_method='moments')
        self.assertEqual(baseline['status'], 'INCONCLUSIVE')
        self.assertEqual(baseline['reason'], 'annular_core_attachment')
        result = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                         boundary_method='moments',
                                         annulus_method='signed_rank_two',
                                         record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['census']['histogram'], c['expected_histogram'])
        certificate = result['certificate']
        self.assertEqual(certificate['schema'], 'normal-cut-handlebodies-signed-annuli-v1')
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],
                                                       c['coordinates'], certificate))
        mutated = deepcopy(certificate)
        mutated['signed_annuli'] = {}
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                                                        c['coordinates'], mutated))
        mutated = deepcopy(certificate)
        mutated['signed_annuli']['source']['passive'][0]['word'][0] *= -1
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                                                        c['coordinates'], mutated))
        mutated = deepcopy(certificate)
        mutated['census']['histogram'][0]['genus'] += 1
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                                                        c['coordinates'], mutated))
        mutated = deepcopy(certificate)
        del mutated['absorption']
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                                                        c['coordinates'], mutated))

    def test_invalid_method_rejected_before_source_processing(self):
        for bad in (None, True, 1, 'whitehead', [], {}):
            with self.assertRaises(ValueError):
                normal_cut_handlebodies({}, [], annulus_method=bad)

    def test_signed_family_after_authenticated_top_reduction(self):
        path = Path(__file__).resolve().parents[1] / 'signed_annulus_research/corpus.json'
        for c in json.loads(path.read_text())['cases'][1:]:
            old = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                          boundary_method='moments')
            self.assertEqual(old['status'], 'INCONCLUSIVE')
            self.assertEqual(old['reason'], 'boundary_kernel_cancellation_stalled')
            result = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                             boundary_method='moments',
                                             annulus_method='signed_rank_two',
                                             record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['census']['histogram'], c['expected_histogram'])
            certificate = result['certificate']
            self.assertEqual(certificate['schema'], 'normal-cut-handlebodies-signed-annuli-v2')
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],
                                                           c['coordinates'], certificate))
            mutated = deepcopy(certificate)
            mutated['core_reduction']['cancellations'][0]['two_handle'] = -1
            self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],
                                                            c['coordinates'], mutated))

    def test_coprime_abelianization_does_not_certify_native_primitivity(self):
        path = Path(__file__).resolve().parents[1] / 'signed_annulus_research/corpus.json'
        c = json.loads(path.read_text())['refusals'][0]
        # The actual transported curve is x^5 y^2.  Its exponent vector is
        # primitive in Z^2, but this curve is not primitive in the free group.
        self.assertEqual(c['exponent_vector'], [5, 2])
        result = normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                         boundary_method='moments',
                                         annulus_method='signed_rank_two',
                                         record_certificate=True)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'annular_core_attachment')
        self.assertNotIn('certificate', result)


if __name__ == '__main__':
    unittest.main()
