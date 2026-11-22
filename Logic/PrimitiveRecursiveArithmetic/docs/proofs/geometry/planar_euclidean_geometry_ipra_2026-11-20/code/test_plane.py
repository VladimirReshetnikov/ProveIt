import unittest
from fractions import Fraction as F
from plane import (Circle, Line, Point, Scalar, between, circle_circle,
                   congruent, line_circle, line_line, nine_point_circle)


class TestPlane(unittest.TestCase):
    def setUp(self):
        self.o = Point(0, 0)
        self.unit = Circle(self.o, 1)

    def test_coincident_endpoints(self):
        p = Point(1, 1)
        self.assertTrue(between(self.o, self.o, self.o))
        self.assertFalse(between(self.o, p, self.o))
        self.assertTrue(between(self.o, p, Point(2, 2)))
        self.assertFalse(between(self.o, Point(-1, -1), p))
        self.assertTrue(congruent(self.o, p, self.o, Point(-1, 1)))

    def test_lines(self):
        a = Line(self.o, Point(1, 1))
        self.assertEqual(line_line(a, Line(Point(1,1), Point(-1,-1))), a)
        self.assertEqual(line_line(a, Line(Point(1,0), a.direction)), ())
        self.assertEqual(line_line(a, Line(Point(1,0), Point(0,1))), (Point(1,1),))
        with self.assertRaises(ValueError):
            Line.through(self.o, self.o)

    def test_line_circle(self):
        a = Line(self.o, Point(1, 1))
        p, q = line_circle(a, self.unit)
        for v in p, q:
            self.assertTrue(a.contains(v) and self.unit.contains(v))
        self.assertEqual(2*q.x, Scalar.rational(2).sqrt())
        self.assertEqual(p.x, -q.x)
        for h, want in [(1, (Point(0,1),)), (2, ())]:
            self.assertEqual(line_circle(Line(Point(0,h), Point(1,0)), self.unit), want)

    def test_circles(self):
        c = Circle(Point(1, 0), 1)
        p, q = circle_circle(self.unit, c)
        self.assertEqual(p.x, F(1, 2))
        self.assertEqual(2*q.y, Scalar.rational(3).sqrt())
        for v in p, q:
            self.assertTrue(self.unit.contains(v) and c.contains(v))
        self.assertEqual(circle_circle(self.unit, Circle(Point(2,0),1)), (Point(1,0),))
        self.assertEqual(circle_circle(self.unit, Circle(Point(3,0),1)), ())
        self.assertEqual(circle_circle(self.unit, self.unit), self.unit)
        zero = Circle(self.o, 0)
        self.assertEqual(circle_circle(zero, zero), (self.o,))
        self.assertEqual(circle_circle(zero, self.unit), ())
        self.assertEqual(circle_circle(zero, c), (self.o,))
        with self.assertRaises(ValueError):
            Circle(self.o, -1)

    def test_nine_points(self):
        for c in [Point(1, 3), Point(0, 3), Point(-2, 2)]:
            circle, mids, feet, euler = nine_point_circle(self.o, Point(4, 0), c)
            self.assertTrue(all(circle.contains(p) for p in (*mids, *feet, *euler)))
        with self.assertRaises(ValueError):
            nine_point_circle(self.o, Point(1,1), Point(2,2))


if __name__ == "__main__":
    unittest.main()
