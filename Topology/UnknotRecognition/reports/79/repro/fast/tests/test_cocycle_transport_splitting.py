import unittest

from transport_research.splitting import splitting_example


class CocycleSplittingTests(unittest.TestCase):
    def test_primitive_coherent_connectivity_is_not_preserved(self):
        result = splitting_example()
        before, after = result['before_census'], result['after_census']
        self.assertEqual((before['components'], before['normal_disks']), (1, 24))
        self.assertEqual((after['components'], after['normal_disks']), (3, 19))
        self.assertEqual([(row['euler_characteristic'], row['multiplicity'])
                          for row in after['component_histogram']], [(1, 1), (2, 2)])


if __name__ == '__main__':
    unittest.main()
