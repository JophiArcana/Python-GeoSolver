
import inspect, cmath, sympy, time
from sympy import conjugate as sycon, im as syim, re as syre, symbols
from sympy import exp as syExp, log as syLog, sqrt as syRt, tan as syTan, cos as syCos, sin as sySin, atan as syAtan, acos as syAcos, asin as syAsin
from sympy import tanh as syTanh, cosh as syCosh, sinh as sySinh, atanh as syAtanh, acosh as syAcosh, asinh as syAsinh
from sympy import Symbol as sySymbol, Add as syAdd, Mul as syMul, Pow as syPow, Mod as syMod, Rational as syRational, Integer as syInt, Float as syFloat
from sympy import solveset, expand, factor, S, Eq
from cmath import sin, cos, sqrt, pi, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh

i, jophi = complex('j'), symbols('jophi')
univ_x, univ_y, univ_z, univ_r, univ_t = symbols('univ_x univ_y univ_z univ_r univ_t')
operators = ['__add__', '__radd__', '__sub__', '__rsub__', '__mul__', '__rmul__', '__truediv__', '__rtruediv__', '__pow__', '__rpow__']

pairs = [(syExp, syLog), (syTan, syAtan), (syCos, syAcos), (sySin, syAsin), (syTanh, syAtanh), (syCosh, syAcosh), (sySinh, syAsinh)]
inverses = {}
for f, g in pairs:
    inverses[f], inverses[g] = g, f

#############################
    # General Functions #
#############################

def stats(p):
    if isinstance(p, Linear):
        return (p.radius, p.angle)
    elif isinstance(p, Circle):
        return (p.center, p.radius)
    elif isinstance(p, Base):
        return p.z
    else:
        return p

def im(z):
    if type(z) == Infinity:
        return Infinity(z.c.imag, z.deg)
    else:
        return z.imag

def re(z):
    if type(z) == Infinity:
        return Infinity(z.c.real, z.deg)
    else:
        return z.real

def arg(z):
    if type(z) == Infinity:
        return cmath.phase(z.c)
    else:
        return cmath.phase(z)

def syarg(z):
    return (syLog(z / syabs(z)) / i).evalf()

def sysqrt(z):
    if z.is_Pow:
        exp = z.args[1]
        if exp % 2 == 0:
            return syPow(z.args[0], int(exp / 2))
        else:
            return syPow(z.args[0], exp / 2)
    else:
        return syRt(z)

def syabs(z):
    return sysqrt(z * sycon(z)).evalf()

def sycis(z):
    return syExp(i * z).evalf()

def syintersect(z1, z2, a1, a2):
    c1, c2 = sycis(-a1), sycis(-a2)
    return ((z1 * c1 ** 2 - z2 * c2 ** 2 - sycon(z1) + sycon(z2)) / (c1 ** 2 - c2 ** 2)).evalf()

def sign(x):
    if x == 0:
        return 0
    else:
        return 1 if x > 0 else -1

def angle(a):
    x = pi - ((pi - a) % (2 * pi))
    if abs(x + pi) < 10 ** -10:
        x = pi
    return x

def directed(a):
    x = pi / 2 - (pi / 2 - a) % pi
    if abs(x + pi / 2) < 10 ** -10:
        x = pi / 2
    return x

def tan(a):
    if abs(a - pi / 2) < 10 ** -10:
        return Infinity()
    elif abs(a + pi / 2) < 10 ** -10:
        return -Infinity()
    else:
        return cmath.tan(a)

def cis(a):
    return complex(cos(a), sin(a))

def con(z):
    if type(z) == sympy.Symbol:
        return sycon(z)
    else:
        return complex(z.real, -z.imag)

conjugate = con

def intersect(z1, z2, a1, a2):
    if abs(angle(a1 - a2)) < 10 ** -10:
        return Infinity(cis(a1))
    else:
        c1, c2 = cis(-a1), cis(-a2)
        return (z1 * c1 ** 2 - z2 * c2 ** 2 - con(z1) + con(z2)) / (c1 ** 2 - c2 ** 2)

def is_constant(expr):
    try:
        return len(expr.free_symbols) == 0
    except:
        return True

def is_mul(expr):
    return type(expr) == syMul and sum(map(lambda arg: 1 - int(is_constant(arg)), expr.args)) > 1

def simplify_eq(eq):
    def f(eq):
        if not (is_constant(eq.lhs) or is_constant(eq.rhs)):
            tyl, tyr = type(eq.lhs), type(eq.rhs)
            if tyl == tyr and len(eq.lhs.args) == len(eq.rhs.args) == 1 and not tyl in [sySin, syCos, syTan]:
                return Eq(eq.lhs.args[0], eq.rhs.args[0])
            elif tyl == syMul or tyr == syMul:
                def g(expr):
                    if type(expr) != syMul:
                        return (expr, 1), 1
                    else:
                        left, right, constant = [], [], []
                        args = expr.args
                        for arg in args:
                            if is_constant(arg):
                                constant.append(arg)
                            elif type(arg) == syPow and arg.args[1] < 0:
                                right.append(1 / arg)
                            else:
                                left.append(arg)
                        return (syMul(*left), syMul(*right)), syMul(*constant)
                glhs, grhs = g(eq.lhs), g(eq.rhs)
                return Eq(glhs[0][0] * grhs[0][1], glhs[0][1] * grhs[0][0] * (grhs[1] / glhs[1]))
            elif tyl == syAdd or tyr == syAdd:
                return Eq(simplify_expr(factor(eq.lhs - eq.rhs)), 0)
            else:
                return eq
        elif is_constant(eq.lhs) and is_constant(eq.rhs):
            return eq
        elif is_constant(eq.lhs):
            return Eq(eq.rhs, eq.lhs)
        elif is_constant(eq.rhs):
            t, lhs, rhs, args = type(eq.lhs), eq.lhs, eq.rhs, eq.lhs.args
            if t == syMul:
                left, right = [], []
                for arg in args:
                    if is_constant(arg) or (type(arg) == syPow and arg.args[1] < 0):
                        right.append(1 / arg)
                    else:
                        left.append(arg)
                return Eq(syMul(*left), rhs * syMul(*right))
            elif t == syAdd:
                if any(is_constant(arg) for arg in args):
                    return Eq(syAdd(*filter(lambda k: not is_constant(k), args)), rhs - syAdd(*filter(lambda k: is_constant(k), args)))
                elif rhs == 0:
                    if len(args) == 2:
                        if type(args[1]) == syMul and -1 in args[1].args:
                            return Eq(args[0], -args[1])
                        else:
                            return eq
                    else:
                        return eq
                else:
                    return Eq(simplify_expr(factor(lhs)), rhs)    
            elif t == syPow:
                return Eq(args[0], syPow(rhs, 1 / args[1]))
            elif t in inverses:
                return Eq(args[0], inverses[t](rhs))
            else:
                return Eq(simplify_expr(factor(lhs)), rhs)
    while hash(eq) != hash(k := f(eq)):
        eq = k
    return Eq(simplify_expr(eq.lhs), simplify_expr(eq.rhs))

def simplify_expr(expr):
    def f(expr):
        t = type(expr)
        if t == sySymbol or isinstance(expr, syRational):
            return expr
        elif t in [list, tuple]:
            return type(expr)([simplify_expr(x) for x in expr])
        elif t in [int, float, syInt, syFloat]:
            if abs(round(expr) - float(expr)) < 10 ** -10:
                return round(expr)
            elif abs(round(2 * expr) - float(2 * expr)) < 10 ** -10:
                return syRational(round(2 * expr), 2)
            else:
                return float(expr)
        elif t in [syAdd, syMul, syPow, syMod]:
            return t(*[simplify_expr(x) for x in expr.args])
        elif t == sycon:
            ex = expr.args[0]
            if type(ex) == sympy.Symbol:
                return expr
            else:
                return type(ex)(*map(sycon, ex.args))
        elif len(expr.args) == 1:
            if len(expand(expr).args) == len(expr.args):
                return t(simplify_expr(expr.args[0]))
            else:
                return sympy.simplify(simplify_expr(expand(expr)))
        else:
            return expr
    while hash(expr) != hash(k := f(expr)):
        expr = k
    return expr

####################
    # Infinity #
####################

class Infinity:
    def __init__(self, coefficient = 1, degree = 1):
        self.c, self.deg = coefficient, degree

    def __repr__(self):
        return f'Infinity({self.c}, {self.deg})'

    # Operator Overloads

    def __eq__(self, x):
        if type(x) == Infinity:
            return abs(self.c - x.c) < 10 ** -10 and abs(self.deg - x.deg) < 10 ** -10
        else:
            return False

    def __neg__(self):
        return Infinity(-self.c, self.deg)

    def __gt__(self, x):
        if self.c < 0:
            return -self < -x
        else:
            if type(x) == Infinity:
                if x.deg > self.deg:
                    return x.c < 0
                elif x.deg == self.deg:
                    return self.c > x.c
                else:
                    return True
            else:
                return self.c > 0

    def __lt__(self, x):
        if self.c < 0:
            return -self > -x
        else:
            if type(x) == Infinity:
                if x.deg > self.deg:
                    return x.c > 0
                elif x.deg == self.deg:
                    return self.c < x.c
                else:
                    return False
            else:
                return self.c < 0

    def __ge__(self, x):
        return self > x or self == x
    
    def __le__(self, x):
        return self < x or self == x

    def __abs__(self):
        return Infinity(abs(self.c), self.deg)

    def __add__(self, x):
        if type(x) == Infinity:
            if x.deg == self.deg:
                return 0 if self.c + x.c == 0 else Infinity(self.c + x.c, self.deg)
            else:
                return max(self, x, key = lambda k: k.deg)
        else:
            return self

    __radd__ = __add__

    def __sub__(self, x):
        return self + -x

    def __rsub__(self, x):
        return -self + x

    def __mul__(self, x):
        if type(x) == Infinity:
            return Infinity(self.c * x.c, self.deg + x.deg)
        else:
            if x == 0:
                return 0
            else:
                return Infinity(self.c * x, self.deg)

    __rmul__ = __mul__

    def __truediv__(self, x):
        if type(x) == Infinity:
            if x.deg > self.deg:
                return 0
            elif x.deg == self.deg:
                return self.c / x.c
            else:
                return Infinity(self.c / x.c, self.deg - x.deg)
        else:
            if x == 0:
                return Infinity(self.c, self.deg + 1)
            else:
                return Infinity(self.c / x, self.deg)

    def __rtruediv__(self, x):
        return 0

    def __pow__(self, x):
        if x < 0:
            return 0
        elif x == 0:
            return 1
        else:
            return Infinity(self.c ** x, self.deg * x)

    def __rpow__(self, x):
        if abs(x) < 1:
            return 0
        elif abs(x) == 1:
            return 1
        else:
            return Infinity(x ** self.c)

    def __abs__(self):
        return Infinity(abs(self.c), self.deg)

######################
    # Base Class #
######################

class Base:
    reverse = [0]
    def __init__(self, *args, name = ''):
        self.name, self.inputs = name.strip(), list(filter(lambda s: type(s) != str, args))
        if isinstance(self, Linear):
            self.var = (symbols(f'{self.name}.radius', real = True), symbols(f'{self.name}.angle', real = True))
        elif isinstance(self, Circle):
            self.var = (symbols(f'{self.name}.z'), symbols(f'{self.name}.radius', real = True))
        else:
            self.var = symbols(f'{self.name}.z')

    def __repr__(self):
        s = f'{type(self).__name__}('
        for p in self.inputs:
            s += f'{p}, '
        return s[:-2] + ')'

    def __hash__(self):
        return hash((hash(type(self)), tuple(tuple(sorted(hash(x) for x in r)) for r in self.references.values())))

    def __eq__(self, p):
        return type(self) == type(p) and hash(self) == hash(p) and (True if not hasattr(self, 'node') else self.node == p.node)

    # Class Methods

    @classmethod
    def formula(cls, x):
        return x

    # Properties

    @property
    def references(self):
        return {'Inputs': self.inputs}

    @property
    def z(self):
        return 0

###################
    # Phantom #
###################

class Phantom(Base):
    reverse, degrees = [0], 2

    # Properties

    @property
    def references(self):
        return {'Value': self.inputs}

    @property
    def z(self):
        return self.inputs[0]

    @property
    def angle(self):
        return arg(self.z)

    @property
    def radius(self):
        return abs(self.z)

    # Operator Overloads

    def __getitem__(self, x):
        assert x in [0, 1]
        return self.z.real if x == 0 else self.z.imag

    def __neg__(self):
        return Phantom(-self.z, name = self.name)

    def __abs__(self):
        return abs(self.z)

########################
    # Three Points #
########################

class Triangulation(Base):
    reverse, degrees = [0, 1, 2], 0

    # Properties

    @property
    def a(self):
        return self.inputs[0]

    @property
    def b(self):
        return self.inputs[1]

    @property
    def c(self):
        return self.inputs[2]

#############################
    # Distance / Angles #
#############################

class Distance(Base):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, az, bz):
        return syabs(az - bz)

    # Properties

    @property
    def references(self):
        return {'Points': self.inputs[:2]}

    @property
    def a(self):
        return self.inputs[0]
        
    @property
    def b(self):
        return self.inputs[1]

    @property
    def z(self):
        return abs(stats(self.a) - stats(self.b))

    # Operator Overloads

    def __gt__(self, d):
        try:
            return self.z > d.z
        except:
            return self.z > d

    def __lt__(self, d):
        try:
            return self.z < d.z
        except:
            return self.z < d

    for s in operators:
        exec(f'def {s}(self, x): return expression(self).{s}(x)')

class DirectedLL(Base):
    reverse, degrees = [0, 1], 0

    # Class Methods
    
    @classmethod
    def formula(cls, l1, l2):
        return syAtan(syTan(l1[1] - l2[1]))

    # Properties

    @property
    def references(self):
        return {'First': [self.inputs[0]], 'Second': [self.inputs[1]]}

    @property
    def l1(self):
        return self.inputs[0]

    @property
    def l2(self):
        return self.inputs[1]

    @property
    def angle(self):
        return directed(self.l2.angle - self.l1.angle)

    @property
    def z(self):
        return directed(self.l2.angle - self.l1.angle)

class Directed(Triangulation):
    reverse = [1, 0, 2]

    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        return syAtan(-i * ((a - b) / (c - b) - (sycon(a) - sycon(b)) / (sycon(c) - sycon(b))) / ((a - b) / (c - b) + (sycon(a) - sycon(b)) / (sycon(c) - sycon(b))))

    # Properties

    @property
    def references(self):
        return {'Angle': [self.inputs[1]], 'Points': [self.inputs[0], self.inputs[2]]}

    @property
    def z(self):
        a, b, c = stats(self.a), stats(self.b), stats(self.c)
        return abs(arg((a - b) / (c - b)))

    @property
    def angle(self):
        a, b, c = stats(self.a), stats(self.b), stats(self.c)
        return abs(arg((a - b) / (c - b)))

class Undirected(Triangulation):
    reverse = [0, 1, 2]

    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        return abs(pi - (pi - syarg(a - b) + syarg(c - b)) % (2 * pi))

    # Properties

    @property
    def references(self):
        return {'First': [self.inputs[0]], 'Angle': [self.inputs[1]], 'Second': [self.inputs[2]]}

    @property
    def z(self):
        a, b, c = stats(self.a), stats(self.b), stats(self.c)
        return (cmath.phase(a - b) - cmath.phase(c - b)) % pi

    @property
    def angle(self):
        a, b, c = stats(self.a), stats(self.b), stats(self.c)
        return (cmath.phase(a - b) - cmath.phase(c - b)) % pi

############################
    # Basic Statements #
############################

class Statement(Base):
    degrees = 0

    # Properties
    
    @property
    def reverse(self):
        return list(range(len(self.inputs)))

class StatementSet(Statement):
    # Properties

    @property
    def references(self):
        return {'Statements': self.inputs}

    @property
    def statements(self):
        return self.inputs

class Equality(Statement):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        if len(args) == 2:
            return args[0] - args[1]
        else:
            return sum((x - sum(args) / len(args)) ** 2 for x in args)

    # Properties

    @property
    def check(self):
        return all(stats(x) == stats(self.inputs[0]) for x in self.inputs[1:])
    
    @property
    def references(self):
        return {'Sides': self.inputs}

###############################
    # Locus and Condition #
###############################

class Locus(Base):
    reverse, degrees = [0, 1], 2
    def __init__(self, *args):
        Base.__init__(self, *args)
        self.requirement = self.inputs[0]
        self.complex_eq = simplify_eq(self.equation(univ_z))
        self.cartesian_eq = simplify_eq(self.eq.subs([(sycon(jophi), univ_x - i * univ_y), (jophi, univ_x + i * univ_y)]))
        self.polar_eq = simplify_eq(self.eq.subs([(sycon(jophi), univ_r / sycis(univ_t)), (jophi, univ_r * sycis(univ_t))]))

    # Properties

    @property
    def references(self):
        return {'Requirement': [self.inputs[0]]}

    @property
    def eq(self):
        expr = pseudo_expression(self.requirement(jophi), jophi)
        try:
            return simplify_eq(Eq(expr.subs([(v, eval(v.name)) for v in expr.free_symbols if v != jophi]), 0))
        except:
            print(expr)

    # Solving Functions

    def equation(self, z):
        return self.eq.subs(jophi, z)

    def solve(self, x = None, y = None):
        if x == None and y == None: 
            return list(solveset(self.eq, jophi))
        elif x == None:
            x = symbols('x')
            return list(solveset(self.equation(x + i * y), x, S.Reals))
        elif y == None:
            y = symbols('y')
            return list(solveset(self.equation(x + i * y), y, S.Reals))
        else:
            return [x + y * i] if x + y * i in self else []

    def x_solve(self, x):
        eq = self.cartesian_eq.subs(univ_x, x)
        return solveset(eq, univ_y, S.Reals).args

    def y_solve(self, y):
        eq = self.cartesian_eq.subs(univ_y, y)
        return solveset(eq, univ_x, S.Reals).args

    def t_solve(self, t):
        eq = self.polar_eq.subs(univ_t, t)
        return solveset(eq, univ_r, S.Reals).args

    # Operator Overloads

    def __contains__(self, p):
        return abs(self.equation(stats(p))) < 10 ** -10

###########################
    # Linear / Circle #
###########################

class Linear(Locus):
    reverse, degrees = [0, 1], 2
    def __init__(self, *args, name = ''):
        Base.__init__(self, *args, name = name)

    # Properties

    @property
    def references(self):
        return {'Radius': [self.inputs[0]], 'Angle': [self.inputs[1]]}

    @property
    def requirement(self):
        expr = expression(self)
        return lambda p: Equality(Directed(0, simplify_expr(expr[0] * sycis(expr[1]) / i), p), pi / 2)

    @property
    def radius(self):
        return abs(self.inputs[0])

    @property
    def angle(self):
        if self.inputs[0] == 0:
            return angle(self.inputs[1])
        else:
            return angle(self.inputs[1] * sign(self.inputs[0]))

    @property
    def z(self):
        return self.radius * cis(self.angle - pi / 2)

    # Operator Overloads

    def __contains__(self, p):
        return im((p.z - self.z) / cis(self.angle)) < 10 ** -10

class Circle(Locus):
    reverse, degrees = [0, 1], 3
    def __init__(self, *args, name = ''):
        Base.__init__(self, *args, name = name)

    # Properties

    @property
    def references(self):
        return {'Center': [self.inputs[0]], 'Radius': [self.inputs[1]]}

    @property
    def requirement(self):
        expr = expression(self)
        return lambda p: Equality(Distance(expr[0], p), expr[1])

    @property
    def center(self):
        try:
            return self.inputs[0].z
        except:
            return self.inputs[0]

    @property
    def radius(self):
        try:
            return self.inputs[1].z
        except:
            return self.inputs[1]

    @property
    def z(self):
        try:
            return self.inputs[0].z
        except:
            return self.inputs[0]

    # Operator Overloads

    def __contains__(self, p):
        return abs(abs(p.z - self.center) - self.radius) < 10 ** -10

trinity = [Phantom, Linear, Circle]
def in_trinity(p):
    return type(p) in trinity

###############################
    # Connect / Intersect #
###############################

class Connect(Linear):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, a, b):
        z = syim(sycon(a) * b) * i / (sycon(a) - sycon(b))
        return (syabs(z), syarg(z))

    # Properties

    @property
    def references(self):
        return {'Points': self.inputs[:2]}

    @property
    def a(self):
        return self.inputs[0]
    
    @property
    def b(self):
        return self.inputs[1]

    @property
    def z(self):
        a, b = self.a.z, self.b.z
        return im(con(a) * b) * i / (con(a) - con(b))

    @property
    def radius(self):
        return abs(self.z) * (-1) ** (-arg(self.z) // pi)

    @property
    def angle(self):
        if abs(self.z) < 10 ** -10:
            return directed(arg(self.a.z - self.b.z))
        else:
            return directed(arg(self.z) + pi / 2)

class IntersectLL(Phantom):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, l1, l2):
        c1, c2 = sycis(-l1[1]), sycis(-l2[1])
        return complex(0, 2) * (-l1[0] * c1 + l2[0] * c2) / (c1 ** 2 - c2 ** 2)

    # Properties

    @property
    def references(self):
        return {'Lines': self.inputs[:2]}

    @property
    def l1(self):
        return self.inputs[0]
    
    @property
    def l2(self):
        return self.inputs[1]

    @property
    def z(self):
        c1, c2 = cis(-self.l1.angle), cis(-self.l2.angle)
        return complex(0, 2) * (-self.l1.radius * c1 + self.l2.radius * c2) / (c1 ** 2 - c2 ** 2)

class IntersectCC(Phantom):
    reverse, degrees = [0, 1], 0

    # Properties

    @property
    def references(self):
        return {'Circles': self.inputs[:2]}

    @property
    def c1(self):
        return min(self.inputs[:2], key = lambda x: id(x))

    @property
    def c2(self):
        return max(self.inputs[:2], key = lambda x: id(x))
    
    @property
    def node(self):
        return self.inputs[2]

    @property
    def z(self):
        o1, o2, r1, r2, d = self.c1.center, self.c2.center, self.c1.radius, self.c2.radius, abs(self.c1.center - self.c2.center)
        a = acos((r1 ** 2 + d ** 2 - r2 ** 2) / (2 * r1 * d))
        return o1 + ((o2 - o1) * r1 / d) * cis(a * (1 if self.node else -1))

    @property
    def formula(self):
        def f(c1, c2):
            o1, o2, r1, r2, d = c1[0], c2[0], c1[1], c2[1], syabs(c1[0] - c2[0])
            a = syAcos((r1 ** 2 + d ** 2 - r2 ** 2) / (2 * r1 * d))
            return o1 + ((o2 - o1) * r1 / d) * sycis(a * (1 if self.node else -1))
        return f

class IntersectLC(Phantom):
    reverse, degrees = [0, 1], 0

    # Properties

    @property
    def references(self):
        return {'Line': [self.inputs[0]], 'Circle': [self.inputs[1]]}

    @property
    def l(self):
        return self.inputs[0]

    @property
    def c(self):
        return self.inputs[1]

    @property
    def node(self):
        return self.inputs[2]

    @property
    def z(self):
        h = Foot(Phantom(self.c.center), self.l).z
        d = sqrt(self.c.radius ** 2 - abs(h - self.c.center) ** 2)
        return h + (h - self.c.center) * (i * d / abs(h - self.c.center)) * (1 if self.node else -1)

    @property
    def formula(self):
        def f(l, c):
            c1 = sycis(l[1])
            z1, z2 = l[0] * c1 / i, c[0]
            h = (z1 + z2 - (sycon(z1) - sycon(z2)) / (c1 ** 2)) / 2
            d = sysqrt(c[1] ** 2 - (h - c[0]) * sycon(h - c[0]))
            return h + (h - c[1]) * (i * d / syabs(h - c[0])) * (1 if self.node else -1)
        return f

def Intersect(a, b, node = True, name = ''):
    if isinstance(a, Linear) and isinstance(b, Linear):
        return IntersectLL(a, b, name = name)
    elif isinstance(a, Circle) and isinstance(b, Circle):
        return IntersectCC(a, b, node, name = name)
    else:
        return IntersectLC(a, b, node, name = name) if isinstance(a, Linear) else IntersectLC(b, a, node, name = name)

####################################
    # Phantom-Linear Relations #
####################################

class Foot(Phantom):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, p, l):
        c, z = sycis(l[1]), l[0] * sycis(l[1]) / i
        return (z + p - (sycon(z) - sycon(p)) / (c ** 2)) / 2

    # Properties

    @property
    def references(self):
        return {'Point': [self.inputs[0]], 'Line': [self.inputs[1]]}

    @property
    def p(self):
        return self.inputs[0]

    @property
    def l(self):
        return self.inputs[1]

    @property
    def z(self):
        return intersect(self.p.z, self.l.z, self.l.angle + pi / 2, self.l.angle)

class ReflectPP(Phantom):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, a, b):
        return 2 * b - a

    # Properties

    @property
    def references(self):
        return {'Point': [self.inputs[0]], 'Reflection': [self.inputs[1]]}

    @property
    def a(self):
        return self.inputs[0]

    @property
    def b(self):
        return self.inputs[1]

    @property
    def z(self):
        return 2 * self.b.z - self.a.z

class ReflectPL(Phantom):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, p, l):
        return 2 * syintersect(p, l[0] * sycis(l[1]) / i, l[1] + pi / 2, l[1]) - p

    # Properties

    @property
    def references(self):
        return {'Point': [self.inputs[0]], 'Reflection': [self.inputs[1]]}

    @property
    def p(self):
        return self.inputs[0]

    @property
    def l(self):
        return self.inputs[1]

    @property
    def z(self):
        return 2 * intersect(self.p.z, self.l.z, self.l.angle + pi / 2, self.l.angle) - self.p.z

class ReflectLP(Linear):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, l, p):
        z = 2 * (p - syintersect(p, l[0] * sycis(l[1]) / i, l[1] + pi / 2, l[1])) + l[0] * sycis(l[1]) / i
        return (syabs(z), syarg(z) + pi / 2) 

    # Properties

    @property
    def references(self):
        return {'Line': [self.inputs[0]], 'Reflection': [self.inputs[1]]}

    @property
    def l(self):
        return self.inputs[0]

    @property
    def p(self):
        return self.inputs[1]

    @property
    def z(self):
        return 2 * (self.p.z - intersect(self.p.z, self.l.z, self.l.angle + pi / 2, self.l.angle)) + self.l.z

    @property
    def radius(self):
        return abs(self.z) * (-1) ** ((pi / 2 - self.l.angle) // pi)

    @property
    def angle(self):
        return directed(self.l.angle)

class ReflectLL(Linear):
    reverse, degrees = [0, 1], 0

    # Class Methods

    @classmethod
    def formula(cls, l1, l2):
        z1, z2 = l1[0] * sycis(l1[1]) / i, l2[0] * sycis(l2[1]) / i
        z = syintersect(syintersect(z1, z2, l1[1], l2[1]), 0, 2 * l2[1] - l1[1], 2 * l2[1] - l1[1] + pi / 2)
        return (syabs(z), syarg(z) + pi / 2)

    # Properties

    @property
    def references(self):
        return {'Line': [self.inputs[0]], 'Reflection': [self.inputs[1]]}

    @property
    def l1(self):
        return self.inputs[0]

    @property
    def l2(self):
        return self.inputs[1]

    @property
    def z(self):
        return intersect(intersect(self.l1.z, self.l2.z, self.l1.angle, self.l2.angle), 0, self.angle, self.angle + pi / 2)

    @property
    def radius(self):
        return abs(self.z) * (-1) ** ((pi / 2 - 2 * self.l2.angle + self.l1.angle) // pi)

    @property
    def angle(self):
        return directed(2 * self.l2.angle - self.l1.angle)

############################
    # Triangle Centers #
############################

class TriangleCenter(Phantom, Triangulation):
    reverse, degrees = [0, 1, 2], 0

    # Properties

    @property
    def references(self):
        return {'Points': self.inputs}

class Circumcenter(TriangleCenter):
    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        n = cycs(lambda p, q: syabs(p) ** 2 * q - syabs(q) ** 2 * p, [a, b, c])
        d = cycs(lambda p, q: 2 * syim(sycon(p) * q) * i, [a, b, c])
        return n / d

    # Properties

    @property
    def z(self):
        inputs = [k.z for k in self.inputs]
        return cycs(lambda x, y: abs(x) ** 2 * y - abs(y) ** 2 * x, inputs) / cycs(lambda x, y: con(x) * y - con(y) * x, inputs)

class Orthocenter(TriangleCenter):
    # Class Methods
    
    @classmethod
    def formula(cls, a, b, c):
        return syintersect(a, b, syarg(b - c) + pi / 2, syarg(c - a) + pi / 2)

    # Properties

    @property
    def z(self):
        a, b, c = self.a.z, self.b.z, self.c.z
        return intersect(a, b, arg(b - c) + pi / 2, arg(c - a) + pi / 2)

class CenterOfMass(Phantom):
    degrees = 0

    # Class Methods

    @classmethod
    def formula(cls, *args):
        return sum(args) / len(args)

    # Properties

    @property
    def references(self):
        return {'Points': self.inputs}

    @property
    def z(self):
        return sum(p.z for p in self.references['Points']) / len(self.references['Points'])

class Centroid(CenterOfMass, TriangleCenter):
    pass

class Midpoint(CenterOfMass):
    reverse = [0, 1]

    #Properties

    @property
    def a(self):
        return self.inputs[0]

    @property
    def b(self):
        return self.inputs[1]

class Incenter(TriangleCenter):
    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        return syintersect(b, c, syarg((a - b) / (c - b)) / 2 + syarg(c - b), syarg((b - c) / (a - c)) / 2 + syarg(a - c))

    # Properties

    @property
    def z(self):
        a, b, c = self.a.z, self.b.z, self.c.z
        mb, mc = arg((a - b) / (c - b)) / 2 + arg(c - b), arg((b - c) / (a - c)) / 2 + arg(a - c)
        return intersect(b, c, mb, mc)

class Excenter(TriangleCenter):
    # Class Methods
    
    @classmethod
    def formula(cls, a, b, c):
        return syintersect(b, c, syarg((a - b) / (c - b)) / 2 + syarg(c - b) + pi / 2, syarg((b - c) / (a - c)) / 2 + syarg(a - c) + pi / 2)

    # Properties

    @property
    def references(self):
        return {'Angle': [self.inputs[0]], 'Points': [self.inputs[1], self.inputs[2]]}

    @property
    def z(self):
        a, b, c = self.a.z, self.b.z, self.c.z
        mb, mc = arg((a - b) / (c - b)) / 2 + arg(c - b), arg((b - c) / (a - c)) / 2 + arg(a - c)
        return intersect(b, c, mb + pi / 2, mc + pi / 2)

class EulerCenter(TriangleCenter):
    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        return (Orthocenter.formula(a, b, c) + Circumcenter.formula(a, b, c)) / 2

    # Properties

    @property
    def z(self):
        return (Orthocenter(*self.inputs).z + Circumcenter(*self.inputs).z) / 2

###################
    # Circles #
###################

class TriangleCircle(Circle, Triangulation):
    degrees = 0

class Circumcircle(TriangleCircle):
    # Class Methods
    
    @classmethod
    def formula(cls, a, b, c):
        return (Circumcenter.formula(a, b, c), syabs(Circumcenter.formula(a, b, c) - a))

    # Properties

    @property
    def z(self):
        return Circumcenter(*self.inputs).z

    @property
    def center(self):
        return Circumcenter(*self.inputs).z

    @property
    def radius(self):
        return abs(self.center - self.a.z)

class Incircle(TriangleCircle):
    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        ic = Incenter.formula(a, b, c)
        d = syintersect(ic, a, syarg(b - a) + pi / 2, syarg(b - a))
        return (ic, syabs(ic - d))

    # Properties

    @property
    def z(self):
        return Incenter(*self.inputs).z

    @property
    def center(self):
        return Incenter(*self.inputs).z

    @property
    def radius(self):
        a, b = self.a.z, self.b.z
        d = intersect(self.center, a, arg(b - a) + pi / 2, arg(b - a))
        return abs(self.center - d)

class Excircle(TriangleCircle):
    # Class Methods

    @classmethod
    def formula(cls, a, b, c):
        ec = Excenter.formula(a, b, c)
        d = syintersect(ec, a, syarg(b - a) + pi / 2, syarg(b - a))
        return (ec, syabs(ec - d))

    # Properties

    @property
    def references(self):
        return {'Angle': [self.inputs[0]], 'Points': [self.inputs[1], self.inputs[2]]}

    @property
    def z(self):
        return Excenter(*self.inputs).z

    @property
    def center(self):
        return Excenter(*self.inputs).z

    @property
    def radius(self):
        a, b = self.a.z, self.b.z
        d = intersect(self.center, a, arg(b - a) + pi / 2, arg(b - a))
        return abs(self.center - d)

##############################
    # Complex Statements #
##############################

class Parallel(Statement):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        return Equality.formula(*[j for i, j in args])

    # Properties
    
    @property
    def check(self):
        return all(abs(l.angle - self.references['Lines'][0].angle) < 10 ** -10 for l in self.references['Lines'])

    @property
    def references(self):
        return {'Lines': list(filter(lambda l: isinstance(l, Linear), self.inputs))}

class Perpendicular(Statement):
    # Class Methods

    @classmethod
    def formula(cls, l1, l2):
        return syTan(l1[1]) * syTan(l2[1]) + 1

    # Properties

    @property
    def check(self):
        return abs(cmath.tan(self.inputs[0].angle) * cmath.tan(self.inputs[1].angle) + 1) < 10 ** -10

    def references(self):
        return {'Lines': self.inputs[:2]}

class Concurrent(Statement):
    # Properties

    @property
    def check(self):
        l1, l2 = self.loci[:2]
        return all(Intersect(l1, l2, True) in l for l in self.loci[2:]) or all(Intersect(l1, l2, False) in l for l in self.loci[2:])

    @property
    def references(self):
        return {'Lines': list(filter(lambda l: isinstance(l, Linear), self.inputs)), 'Circles': list(filter(lambda c: isinstance(c, Circle), self.inputs))}

    @property
    def loci(self):
        return self.references['Lines'] + self.references['Circles']

    # Condition Expression

    def expr(self, z):
        l1, l2 = self.loci[:2]
        x = expression(Intersect(l1, l2, all(Intersect(l1, l2, True) in l for l in self.loci[2:])), z)
        s = 0
        for l in self.loci[2:]:
            expr = expression(l, z)
            if isinstance(l, Linear):
                eq = (x / sycis(expr[1]) + expr[0] * i) - (sycon(x) * sycis(expr[1]) - expr[0] * i)
            else:
                eq = syabs(x - expr[0]) - expr[1]
            s += eq ** 2
        return s

class ConcurrentPoint(Concurrent):
    # Properties

    @property
    def check(self):
        return all(self.point in l for l in self.loci)

    @property
    def references(self):
        d = {'Point': [self.inputs[0]]}
        d['Lines'], d['Circles'] = list(filter(lambda l: isinstance(l, Linear), self.inputs[1:])), list(filter(lambda c: isinstance(c, Circle), self.inputs[1:]))
        return d

    @property
    def point(self):
        return self.inputs[0]

    @property
    def loci(self):
        return self.references['Lines'] + self.references['Circles']

    # Condition Expression

    def expr(self, z):
        x = expression(self.point, z)
        s = 0
        for l in self.loci:
            expr = expression(l, z)
            if isinstance(l, Linear):
                eq = (x / sycis(expr[1]) + expr[0] * i) - (sycon(x) * sycis(expr[1]) - expr[0] * i)
            else:
                eq = syabs(x - expr[0]) - expr[1]
            s += eq ** 2
        return s

class Collinear(Statement):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        f = lambda a, b, c: (cycs(lambda p, q: 2 * syim(p * sycon(q)) * i, [a, b, c])) ** 2
        return cycs(f, args)

    # Properties

    @property
    def check(self):
        return all(p in Connect(*self.references['Points'][:2]) for p in self.references['Points'][2:])

    @property
    def references(self):
        return {'Points': list(filter(lambda p: isinstance(p, Phantom), self.inputs))}

class CollinearLine(Collinear):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        l = args[0]
        return sum(((x / sycis(l[1]) + l[0] * i) - (sycon(x) * sycis(l[1]) - l[0] * i)) ** 2 for x in args[1:])

    # Properties

    @property
    def check(self):
        return all(p in self.line for p in self.references['Points'])

    @property
    def references(self):
        return {'Line': [self.inputs[0]], 'Points': list(filter(lambda p: isinstance(p, Phantom), self.inputs[1]))}

    @property
    def line(self):
        return self.inputs[0]

class Cyclic(Statement):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        def f(a, b, c, d):
            def g(x):
                return ((a - x) * (sycon(b) - sycon(x))) / ((b - x) * (sycon(a) - sycon(x)))
            return (g(c) - g(d)) ** 2
        return cycs(f, args)

    # Properties

    @property
    def check(self):
        return all(p in Circumcircle(*self.references['Points'][:3]) for p in self.references['Points'][3:])

    @property
    def references(self):
        return {'Points': list(filter(lambda p: isinstance(p, Phantom), self.inputs))}

class CyclicCircle(Statement):
    # Class Methods

    @classmethod
    def formula(cls, *args):
        c = args[0]
        return sum((syabs(c[0] - x) - c[1]) ** 2 for x in args[1:])

    # Properties

    @property
    def check(self):
        return all(p in self.circle for p in self.references['Points'])

    @property
    def references(self):
        return {'Circle': [self.inputs[0]], 'Points': list(filter(lambda p: isinstance(p, Phantom), self.inputs[1]))}

    @property
    def circle(self):
        return self.inputs[0]

class Expression(Statement):
    # Properties

    @property
    def check(self):
        return self.inputs[0](*[v.z for v in self.references['Variables']])

    @property
    def references(self):
        return {'Expression': [self.inputs[0]], 'Variables': self.inputs[1:]}

    @property
    def formula(self):
        return self.inputs[0]    

####################
    # Theorems #
####################

class Theorem(Base):
    # Properties

    @property
    def references(self):
        return {'Given': [self.inputs[0]], 'Result': [self.inputs[1]]}

    @property
    def given(self):
        return self.inputs[0]

    @property
    def result(self):
        return self.inputs[1]

    @property
    def given_variables(self):
        return [[func(s) for func in find_in_diagram(s, in_trinity)] for s in self.given.inputs]

    @property
    def result_variables(self):
        return [[func(s) for func in find_in_diagram(s, in_trinity)] for s in self.result.inputs]

    @property
    def index_link(self):
        gv = sum(self.given_variables, [])
        return [[gv.index(r) for r in rv] for rv in self.result_variables]

####################
    # Analysis #
####################

def typetree(t):
    if in_trinity(t):
        return Tree(type(t))
    else:
        r = t.references
        return Tree(type(t), [Tree(list(r.keys())[i], [typetree(x) for x in list(r.values())[i]]) for i in range(len(r))])

def objtree(t):
    if in_trinity(t) or not isinstance(t, Base):
        return Tree(t)
    else:
        return Tree(t, [objtree(b) for b in sum(list(t.references.values()), [])])

def hashtree(t):
    if in_trinity(t):
        return Tree(hash(t))
    else:
        return Tree(hash(t), [hashtree(b) for b in sum(list(t.references.values()), [])])

def inputtree(p):
    if not isinstance(p, Base):
        return Tree(p)
    else:
        return Tree(type(p), [inputtree(i) for i in p.inputs])

def convert_inputtree(t):
    if type(t.label) != type:
        return t.label
    else:
        return t.label(*[convert_inputtree(b) for b in t.branches])

def find_property(t, f):
    funcs = []
    if f(t.label):
        funcs.append(lambda t: t.label)
    def finder(i, func):
        return lambda v: func(v.branches[i])
    for i in range(len(t.branches)):
        for func in find_property(t.branches[i], f):
            funcs.append(finder(i, func))
    return funcs

def find_tree(t, f):
    funcs = []
    if f(t.label):
        funcs.append(lambda t: t)
    def finder(i, func):
        return lambda v: func(v.branches[i])
    for i in range(len(t.branches)):
        for func in find_tree(t.branches[i], f):
            funcs.append(finder(i, func))
    return funcs

def find_in_diagram(p, f):
    funcs = []
    if f(p):
        funcs.append(lambda p: p)
    for k in p.references:
        for i in range(len(p.references[k])):
            for func in find_in_diagram(p.references[k][i], f):
                funcs.append(lambda p: func(p.references[k][i]))
    return funcs

def interchangeable(x, y):
    try:
        return x.node ^ y.node
    except AttributeError:
        if not (type(x) == type(y) and hash(x) == hash(y)):
            return False
        elif not (hasattr(x, 'node') and hasattr(y, 'node')):
            return True

def applicable(t, p):
    ot, op = objtree(t), objtree(p)
    l = find_property(ot, in_trinity)
    t_leaves, p_leaves = list(map(lambda f: f(ot), l)), list(map(lambda f: f(op), l))
    b = True
    for i in range(len(t_leaves) - 1):
        for j in range(i, len(t_leaves)):
            if hashtree(t_leaves[i]) == hashtree(t_leaves[j]):
                b = b and hashtree(p_leaves[i]) == hashtree(p_leaves[j])
    return b

def reformat(p, t):
    if not typetree(p).is_continuation(typetree(t)):
        return []
    elif typetree(t).is_leaf():
        return [p]
    else:
        # Possible rearrangements of p and list of total reformats for each reference category e.g. [[Angle reformats], [Point reformats]] form [[[a, b, c], [a, b, c]], []]
        p_rearrange, d = [], []
        for k in p.references:
            # p and t reference objects for a certain category
            pk, tk = p.references[k], t.references[k]
            possibilities = []
            # If a permutation of reference objects work, add the list of possibilities of reformatting each individual object
            for l in permute_list(len(pk)):
                if all(map(lambda i: typetree(pk[l[i]]).is_continuation(typetree(tk[i])), range(len(pk)))):
                    possibilities += list_mul(*map(lambda i: reformat(pk[l[i]], tk[i]), range(len(pk))))
            d.append(possibilities)
        dual = find_property(objtree(t), lambda t: hasattr(t, 'node'))
        for r in list_mul(*d):
            inputs = [sum(r, [])[p.reverse[i]] for i in range(sum(map(lambda k: int(type(k) != bool), p.inputs)))]
            p2 = type(p)(p.name, *inputs) if not hasattr(p, 'node') else type(p)(p.name, *inputs, p.node)
            tp2, tt, total = objtree(p2), objtree(t), True
            for i in range(len(dual) - 1):
                for j in range(i + 1, len(dual)):
                    fi, fj = dual[i], dual[j]
                    total = total and interchangeable(fi(tp2), fj(tp2)) == interchangeable(fi(tt), fj(tt))
            if total:
                p_rearrange.append(p2)
        return list(filter(lambda k: applicable(t, k), p_rearrange))

def apply(t, s):
    reformats, applications = reformat(s, t.given), []
    iptg, iptr = inputtree(t.given), inputtree(t.result)
    l = find_tree(iptg, lambda k: k in trinity)
    for r in reformats:
        ipr = inputtree(r)
        d = {convert_inputtree(func(iptg)): convert_inputtree(func(ipr)) for func in l}
        rep = replicate(iptr)
        def change_leaves(k):
            list(map(change_leaves, k.branches))
            if k.label in trinity:
                value = inputtree(d[convert_inputtree(k)])
                k.label, k.branches = value.label, value.branches
        change_leaves(rep)
        applications.append(convert_inputtree(rep))
    return applications

def uses(p, z):
    return p == z or (False if not isinstance(p, Base) else any(uses(k, z) for k in p.inputs))

def pseudo_expression(p, *args):
    if not args:
        if not isinstance(p, Base):
            return p
        elif type(p) in trinity:
            return p.var
        else:
            return p.formula(*map(lambda v: pseudo_expression(v), p.inputs))
    else:
        if not isinstance(p, Base):
            return p
        elif p in args or (type(p) in trinity) or (not any(uses(p, z) for z in args)):
            return p.var
        else:
            return p.formula(*map(lambda v: pseudo_expression(v, *args), p.inputs))

def expression(p, *args):
    return simplify_expr(pseudo_expression(p, *args))

###################
    # Support #
###################

def cycs(f, s):
    return sum(f(*[s[(i + j) % len(s)] for j in range(len(inspect.signature(f).parameters))]) for i in range(len(s)))

def syms(f, s):
    return sum(sum(f(*p) for p in permutations(sub)) for sub in subsets(s, len(inspect.signature(f).parameters)))

def list_mul(*args):
    if len(args) == 1:
        return [[i] for i in args[0]]
    else:
        return [[i] + j for i in args[0] for j in list_mul(*args[1:])]

def all_equal(l):
    return all(all(l[i] == l[j] for j in range(i + 1, len(l))) for i in range(len(l) - 1))

def permute(l, p):
    assert len(l) == len(p)
    l2 = l[:]
    for i in range(len(l)):
        l[i] = l2[p[i]]

def permute_list(n):
    assert n >= 0
    if n <= 1:
        return [[0]] if n == 1 else []
    else:
        f = []
        for l in permute_list(n - 1):
            for i in range(n):
                l2 = l[:]
                l2.insert(i, n - 1)
                f.append(l2)
        return f

def permutations(l):
    return [[l[p[i]] for i in range(len(l))] for p in permute_list(len(l))]

def subsets(s, n):
    if n > len(s) or n < 0:
        return []
    elif n == len(s):
        return [s]
    elif n == 0:
        return [[]]
    else:
        return subsets(s[1:], n) + [[s[0]] + sub for sub in subsets(s[1:], n - 1)]

def replicate(t):
    return Tree(t.label, [replicate(b) for b in t.branches])

class fRange:
    def __init__(self, x, y):
        self.min, self.max = min(x, y), max(x, y)
    
    def __repr__(self):
        return f'fRange({self.min}, {self.max})'

    def __contains__(self, s):
        return self.min < s < self.max

class Tree:
    def __init__(self, label, branches = []):
        for b in branches:
            assert isinstance(b, Tree)
        self.label = label
        self.branches = list(branches)

    def is_leaf(self):
        return not self.branches

    def map(self, fn):
        self.label = fn(self.label)
        for b in self.branches:
            b.map(fn)

    def __repr__(self):
        if self.branches:
            branch_str = ', ' + repr(self.branches)
        else:
            branch_str = ''
        if type(self.label) == type:
            return f'Tree({self.label.__name__}{branch_str})'
        else:
            return f'Tree({self.label}{branch_str})'

    def __str__(self):
        def print_tree(t, indent = 0):
            tree_str = '  ' * indent + str(t.label) + "\n"
            for b in t.branches:
                tree_str += print_tree(b, indent + 1)
            return tree_str
        return print_tree(self).rstrip()

    def __eq__(self, t):
        if self.is_leaf():
            return t.is_leaf() and self.label == t.label
        elif type(self.label) == type:
            if not (self.label == t.label and (k := len(self.branches)) == len(t.branches)):
                return False
            else:
                return all(self.branches[i] == t.branches[i] for i in range(k))
        else:
            if not (self.label == t.label and (k := len(self.branches)) == len(t.branches)):
                return False
            else:
                return any(all(self.branches[l[i]] == t.branches[i] for i in range(k)) for l in permute_list(k))

    def __iter__(self):
        yield self.label
        for b in self.branches:
            yield from b

    def __contains__(self, t):
        if type(t) == Tree:
            return self.is_continuation(t) or any(b.is_continuation(t) for b in self.branches)
        else:
            return self.label == t or any(t in b for b in self.branches)

    def is_continuation(self, t):
        if t.is_leaf():
            if type(t.label) == type:
                return issubclass(self.label, t.label)
            else:
                return self.label == t.label
        elif type(self.label) == type:
            if not (self.label == t.label and (k := len(self.branches)) == len(t.branches)):
                return False
            else:
                return all(self.branches[i].is_continuation(t.branches[i]) for i in range(k))
        else:
            if not (self.label == t.label and (k := len(self.branches)) == len(t.branches)):
                return False
            else:
                return any(all(self.branches[l[i]].is_continuation(t.branches[i]) for i in range(k)) for l in permute_list(k))

