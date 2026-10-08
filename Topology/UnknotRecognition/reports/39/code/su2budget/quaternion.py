"""Hamilton multiplication, valid over any commutative coefficient ring."""
def multiply(p, q):
    a, b, c, d = p
    e, f, g, h = q
    return (a*e-b*f-c*g-d*h,
            a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f,
            a*h+b*g-c*f+d*e)


def conjugate(q):
    return (q[0], -q[1], -q[2], -q[3])


def cross(u, v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2],
            u[0]*v[1]-u[1]*v[0])


def noncommutativity(quaternions):
    return sum(z*z for i, q in enumerate(quaternions)
               for p in quaternions[:i] for z in cross(p[1:], q[1:]))
