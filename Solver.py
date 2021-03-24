
import cmath, math
from MusashiAlter import *
from cmath import e, exp

#############################
    # General Functions #
#############################

def union(*args):
    if len(args) == 0:
        return set()
    elif len(args) == 1:
        return args[0]
    else:
        return args[0].union(*args[1:])

def intersection(*args):
    if len(args) == 0:
        return set()
    elif len(args) == 1:
        return args[0]
    else:
        return intersection(args[0].intersection(args[1]), *args[2:])

def is_constant(x):
    return type(x) in [complex, int, float, Rational, Infinity]

def is_real(x):
    return type(x) in [int, float, Rational]

def is_log(expr):
    return type(expr) == Log or (type(expr) == Mul and any(type(arg) == Log for arg in expr.args))

def integerize(x):
    if type(x) == float:
        return round(x) if abs(round(x) - x) < 10 ** -10 else x
    elif type(x) == complex:
        re = round(x.real) if abs(round(x.real) - x.real) < 10 ** -10 else x.real
        im = round(x.imag) if abs(round(x.imag) - x.imag) < 10 ** -10 else x.imag
        return complex(re, im) if im != 0 else re
    else:
        return x

def cpx_round(x):
    if type(x) in [int, float]:
        return round(x)
    elif type(x) == complex:
        return complex(round(x.real), round(x.imag)) if round(x.imag) != 0 else round(x.real)
    else:
        return x

def sqrt(x):
    if is_constant(x):
        return x ** 0.5
    else:
        return Pow(x, Rational.half)

def sign(expr):
    if is_constant(expr):
        if type(expr) == Infinity:
            return sign(expr.c)
        elif integerize(expr) == 0:
            return 0
        else:
            return 1 if expr > 0 else -1
    elif type(expr) == Mul:
        if is_constant(expr.args[0]):
            return sign(expr.args[0])
        else:
            return 1
    elif type(expr) == Add:
        return sign(sum(map(sign, expr.args)))
    else:
        return 1

def gcd(*args):
    if len(args) == 1:
        return args[0]
    elif all(map(is_constant, args)):
        if len(args) == 2:
            x, y = integerize(args[0]), integerize(args[1])
            if type(x) == type(y) == int:
                return math.gcd(x, y)
            elif type(x) == int and type(y) == Rational:
                return Rational(math.gcd(x, y.args[0]), y.args[1])
            elif type(x) == Rational and type(y) == int:
                return Rational(math.gcd(y, x.args[0]), x.args[1])
            elif type(x) == type(y) == Rational:
                return Rational(math.gcd(x.args[0], y.args[0]), round(x.args[1] * y.args[1] / math.gcd(x.args[1], y.args[1])))
            else:
                return 1
    elif len(args) == 2 and is_constant(args[0]) and not is_constant(args[1]):
        if type(args[1]) == Mul and is_constant(args[1].args[0]):
            return gcd(args[0], args[1].args[0])
        else:
            return 1
    elif len(args) == 2 and not is_constant(args[0]) and is_constant(args[1]):
        if type(args[0]) == Mul and is_constant(args[0].args[0]):
            return gcd(args[1], args[0].args[0])
        else:
            return 1
    elif len(args) == 2 and not is_constant(args[0]) and not is_constant(args[1]):
        x, y = args
        def f(r):
            if type(r) == Pow:
                return {r.args[0] : r.args[1]}
            elif type(r) != Mul:
                return {r: 1}
            else:
                dr = dict()
                for arg in r.args:
                    if type(arg) == Pow:
                        if arg.args[0] in dr:
                            dr[arg.args[0]] += arg.args[1]
                        else:
                            dr[arg.args[0]] = arg.args[1]
                    else:
                        if arg in dr:
                            dr[arg] += 1
                        else:
                            dr[arg] = 1
                return dr
        dx, dy = f(x), f(y)
        keys = set(list(dx.keys()) + list(dy.keys()))
        gcd_list = dict()
        for key in keys:
            f = lambda k, d: 0 if k not in d else d[k]
            gcd_list[key] = min(f(key, dx), f(key, dy))
        return Mul(*[Pow(k, gcd_list[k]) for k in gcd_list])
    else:
        return gcd(args[0], gcd(args[1:]))

def lcm(*args):
    if len(args) == 1:
        return args[0]
    elif len(args) == 2:
        if is_constant(args[0]) and is_constant(args[1]):
            return Rational(args[0] * args[1] / gcd(args[0], args[1]))
        else:
            return args[0] * args[1] / gcd(args[0], args[1])
    else:
        return lcm(args[0], lcm(args[1:]))

def cis(t):
    return Exp(t * i)

def phase(z):
    return Log(z / Conjugate(z)) / (2 * i)

def real(z):
    return (z + Conjugate(z)) / 2

def imag(z):
    return (z - Conjugate(z)) / (2 * i)

def remove_constant(expr):
    if type(expr) == Mul and is_constant(expr.args[0]):
        return Mul(*expr.args[1:])
    else:
        return expr

def get_exponent(expr):
    if type(expr) == Pow:
        return expr.args[1]
    else:
        return 1

def remove_exponent(expr):
    if type(expr) == Pow:
        return expr.args[0]
    else:
        return expr

def prod(l):
    p = 1
    for arg in l:
        p *= arg
    return p

def nlogn_search(l):
    l2 = sorted(l, key = hash)
    return any(l2[i] == l2[i + 1] for i in range(len(l2) - 1))

def is_mul_of(expr, t):
    return isinstance(expr, t) or (type(expr) == Mul and len(expr.args) == 2 and is_constant(expr.args[0]) and isinstance(expr.args[1], t))

def binom(a, b):
    return round(math.factorial(a) / (math.factorial(b) * math.factorial(a - b)))

'''
def expand(expr):
    if type(expr) == Mul or (type(expr) == Pow and type(expr.args[1]) == int):
        if (type(expr) == Mul and any(map(lambda x: type(x) == Add, expr.args))) or (type(expr) == Pow and type(expr.args[0]) == Add):
            list_terms = lambda expr: (expr, ) if type(expr) != Add else expr.args
            if type(expr) == Mul:
                return Add(Mul(*terms) for terms in list_mul(*map(list_terms, expr.args)))
            elif expr.args[1] > 0:
                return Add(Mul(*terms) for terms in list_mul(*[list_terms(expr.args[0])] * expr.args[1]))
            else:
                return 1 / Add(Mul(*terms) for terms in list_mul(*[list_terms(expr.args[0])] * -expr.args[1]))
    return expr
'''

def expand(expr):
    if is_constant(expr) or type(expr) == Symbol:
        return expr
    else:
        k = type(expr)(*map(expand, expr.args))
        if is_constant(k) or type(k) == Symbol:
            return k
        else:
            return k.expand()

####################
    # Rational #
####################

class Rational:
    def __new__(cls, *args):
        assert len(args) <= 2
        # Convert single argument to Rational
        if len(args) == 1:
            if type(args[0]) == Rational:
                return args[0]
            args = integerize(args[0])
            if type(args) == int:
                return args
            for i in range(2, 101):
                if abs(round(args * i) - args * i) < 10 ** -6:
                    return Rational(round(args * i), i)
            return args
        # Flatten Rational arguments
        elif type(args[0]) == Rational:
            return Rational(args[0].args[0], args[0].args[1] * args[1])
        elif type(args[1]) == Rational:
            return Rational(args[0] * args[1].args[1], args[1].args[0])
        # Convert floats to 1 argument
        elif type(args[0]) == float or type(args[1]) == float:
            return Rational(args[0] / args[1])
        else:
            cd = math.gcd(*args)
            num, dem = int(args[0] / cd), int(args[1] / cd)
            if dem < 0:
                num, dem = -num, -dem
            if dem == 1:
                return num
            else:
                new = super(Rational, cls).__new__(cls)
                new.args = (num, dem)
                return new

    def __repr__(self):
        return f'{self.args[0]} / {self.args[1]}'

    def __hash__(self):
        return hash((type(self), self.args))

    # Operator Overloads

    def __eq__(self, r):
        if type(r) == Rational:
            return self.args[0] == r.args[0] and self.args[1] == r.args[1]
        else:
            return abs(self.args[0] / self.args[1] - r) < 10 ** -10

    def __abs__(self):
        return Rational(abs(self.args[0]), self.args[1])

    def __neg__(self):
        return Rational(-self.args[0], self.args[1])

    def __gt__(self, r):
        if type(r) == Rational:
            return self.args[0] / self.args[1] > r.args[0] / r.args[1]
        else:
            return self.args[0] / self.args[1] > r
    
    def __lt__(self, r):
        if type(r) == Rational:
            return self.args[0] / self.args[1] < r.args[0] / r.args[1]
        else:
            return self.args[0] / self.args[1] < r

    def __ge__(self, r):
        return self > r or self == r

    def __le__(self, r):
        return self < r or self == r

    def __add__(self, r):
        if type(r) == Rational:
            return Rational(self.args[0] * r.args[1] + self.args[1] * r.args[0], self.args[1] * r.args[1])
        elif type(c := integerize(r)) == int:
            return Rational(self.args[0] + c * self.args[1], self.args[1])
        else:
            return Rational(self.args[0] / self.args[1] + r)
    
    __radd__ = __add__

    def __sub__(self, r):
        return self + -r
    
    def __rsub__(self, r):
        return -self + r

    def __mul__(self, r):
        if type(r) == Rational:
            return Rational(self.args[0] * r.args[0], self.args[1] * r.args[1])
        elif type(c := integerize(r)) == int:
            return Rational(self.args[0] * c, self.args[1])
        else:
            return Rational(self.args[0] * r / self.args[1])

    __rmul__ = __mul__

    def __truediv__(self, r):
        if type(r) == Rational:
            return Rational(self.args[0] * r.args[1], self.args[1] * r.args[0])
        elif type(c := integerize(r)) == int:
            return Rational(self.args[0], self.args[1] * c)
        else:
            return Rational(self.args[0] / (self.args[1] * r))

    def __rtruediv__(self, r):
        if type(c := integerize(r)) == int:
            return Rational(c * self.args[1], self.args[0])
        else:
            return Rational(r * self.args[1], self.args[0])

    def __pow__(self, r):
        if is_constant(r):
            return Rational(self.args[0] ** r, self.args[1] ** r)
        else:
            return Pow(self, r)

    def __rpow__(self, r):
        if is_constant(r):
            return Rational(r ** (self.args[0] / self.args[1]))
        else:
            return Pow(r, self)

Rational.half = Rational(1, 2)

###############################
    # Expression / Symbol #
###############################

class Expression:
    def __eq__(self, expr):
        return type(self) == type(expr) and sorted(self.args, key = hash) == sorted(expr.args, key = hash)

    def __hash__(self):
        return hash((type(self), tuple(sorted(map(hash, self.args)))))

    def __repr__(self):
        return f'{type(self).__name__}({", ".join(map(repr, self.args))})'

    # Operator Overloads

    def __neg__(self):
        return Mul(-1, self)

    def __abs__(self):
        return self if sign(self) == 1 else -self

    def __gt__(self, expr):
        dif = self - expr
        return dif.subs([(sym, Infinity()) for sym in dif.free_symbols]) > 0

    def __lt__(self, expr):
        dif = self - expr
        return dif.subs([(sym, Infinity()) for sym in dif.free_symbols]) < 0

    def __ge__(self, expr):
        return self == expr or self > expr

    def __le__(self, expr):
        return self == expr or self < expr

    def __ne__(self, expr):
        return not self == expr

    def __add__(self, expr):
        return Add(self, expr)

    __radd__ = __add__

    def __sub__(self, expr):
        return Add(self, Mul(-1, expr))

    def __rsub__(self, expr):
        return Add(Mul(-1, self), expr)

    def __mul__(self, expr):
        return Mul(self, expr)

    __rmul__ = __mul__

    def __truediv__(self, expr):
        return Mul(self, Pow(expr, -1))

    def __rtruediv__(self, expr):
        return Mul(Pow(self, -1), expr)

    def __pow__(self, expr):
        return Pow(self, expr)

    def __rpow__(self, expr):
        return Pow(expr, self)

    # Substitution / Variables

    def subs(self, *args):
        assert len(args) == 2 or (len(args) == 1 and type(args[0]) == list)
        if len(args) == 2:
            if type(self) == Symbol:
                return args[1] if self == args[0] else self
            else:
                if self == args[0]:
                    return args[1]
                else:
                    return type(self)(*[arg if not isinstance(arg, Expression) else arg.subs(*args) for arg in self.args])
        else:
            if len(args[0]) == 0:
                return self
            else:
                s = self.subs(*args[0][0])
                if not isinstance(s, Expression):
                    return s
                else:
                    return s.subs(args[0][1:])

    @property
    def free_symbols(self):
        if type(self) == Symbol:
            return {self}
        else:
            return union(*map(lambda arg: arg.free_symbols, filter(lambda arg: isinstance(arg, Expression), self.args)))

    def expand(self):
        return self

class Symbol(Expression):
    def __init__(self, s):
        self.args = (s, )

    def __new__(cls, s):
        if ' ' not in s:
            return object.__new__(cls)
        else:
            return tuple(map(Symbol, s.split()))

    def __repr__(self):
        return self.args[0]

    # Properties

    @property
    def name(self):
        return self.args[0]

############################
    # Core Expressions #
############################

#####################
    # Add / Mul #
#####################

class Add(Expression):
    def __new__(cls, *args):
        # If there are no arguments return 0
        if len(args) == 0:
            return 0
        # If there is only one argument return original expression
        if len(args) == 1:
            return args[0]
        # Flatten any Add arguments to a list of their arguments
        elif any(type(arg) == Add for arg in args):
            l = []
            for arg in args:
                if type(arg) == Add:
                    l.extend(arg.args)
                else:
                    l.append(arg)
            return Add(*l)
        # Pull out constants
        elif any(is_mul_of(arg, Add) and is_constant(arg.args[1].args[0]) for arg in args):
            l = []
            for arg in args:
                if is_mul_of(arg, Add) and is_constant(arg.args[1].args[0]):
                    l.extend([arg.args[0] * arg.args[1].args[0], Mul(arg.args[0], Add(*arg.args[1].args[1:]))])
                else:
                    l.append(arg)
            return Add(*l)
        # Combine constants and move to the front
        elif (s := sum(map(lambda x: int(is_constant(x)), args))) > 1:
            constant, other = [], []
            for arg in args:
                if is_constant(arg):
                    constant.append(arg)
                else:
                    other.append(arg)
            const = sum(constant)
            if integerize(const) == 0:
                return Add(*other)
            else:
                return Add(sum(constant), *other) if abs(sum(constant)) > 10 ** -10 else Add(*other)
        # Move constant to the front if only one
        elif s > 0 and not is_constant(args[0]):
            constant, other = [], []
            for arg in args:
                if is_constant(arg):
                    constant.append(arg)
                else:
                    other.append(arg)
            return Add(constant[0], *other) if abs(constant[0]) > 10 ** -10 else Add(*other)
        # Remove constant 0
        elif is_constant(args[0]) and integerize(args[0]) == 0:
            return Add(*args[1:])
        # Integerize constant
        elif is_constant(args[0]) and type(args[0]) != type(integerize(args[0])):
            return Add(integerize(args[0]), *args[1:])
        # Combine like terms
        terms = []
        for arg in args:
            if type(arg) == Mul and len(arg.args) == 2 and is_constant(arg.args[0]) and type(arg.args[1]) == Add:
                for x in arg.args[1].args:
                    terms.append(Mul(arg.args[0], x))
            else:
                terms.append(arg)
        if nlogn_search(list(map(remove_constant, terms))):
            d = dict()
            for term in terms:
                if type(term) == Mul and is_constant(term.args[0]):
                    if (p := Mul(*term.args[1:])) in d:
                        d[p] += term.args[0]
                    else:
                        d[p] = term.args[0]
                else:
                    if term in d:
                        d[term] += 1
                    else:
                        d[term] = 1
            return Add(*[(k if d[k] == 1 else Mul(d[k], k)) for k in d])
        # Factor out gcd
        elif (g := gcd(*args)) != 1:
            return Mul(g, Add(*[arg / g for arg in args]))
        # Condense logarithms
        elif sum(map(lambda arg: int(is_log(arg)), args)) > 1:
            logs, other = [], []
            for arg in args:
                if is_log(arg):
                    if type(arg) == Log:
                        logs.append(arg.args[0])
                    else:
                        c = 0
                        for i in range(len(arg.args)):
                            if type(arg.args[i]) == Log:
                                c = i
                                break
                        logs.append(Pow(arg.args[c].args[0], Mul(*(arg.args[:c] + arg.args[c + 1:]))))
                else:
                    other.append(arg)
            return Add(*other, Log(Mul(*logs)))
        else:
            new = super(Add, cls).__new__(cls)
            new.args = args
            return new

    def __repr__(self):
        return ' + '.join(map(str, self.args))

    # Manipulation

    def expand(self):
        return Add(*[arg if is_constant(arg) else arg.expand() for arg in self.args])

class Mul(Expression):
    def __new__(cls, *args):
        # If there are no arguments return 1
        if len(args) == 0:
            return 1
        # If there is only one argument return original expression
        if len(args) == 1:
            return args[0]
        # Flatten any Mul arguments to a list of their arguments
        elif any(type(arg) == Mul for arg in args):
            l = []
            for arg in args:
                if type(arg) == Mul:
                    l.extend(arg.args)
                else:
                    l.append(arg)
            return Mul(*l)
        # Combine constants and move to the front
        elif (s := sum(map(lambda x: int(is_constant(x)), args))) > 1:
            constant, other = [], []
            for arg in args:
                if is_constant(arg):
                    constant.append(arg)
                else:
                    other.append(arg)
            const = prod(constant)
            if abs(const) < 10 ** -10:
                return 0
            elif abs(const - 1) < 10 ** -10:
                return Mul(*other)
            else:
                return Mul(const, *other)
        # Remove constant term 1 or 0
        elif is_constant(args[0]):
            if args[0] == 0:
                return 0
            else:
                return Mul(*args[1:])
        # Integerize constant
        elif is_constant(args[0]) and type(args[0]) != type(integerize(args[0])):
            return Mul(integerize(args[0]), *args[1:])
        # Split powers
        elif any(type(arg) == Pow and type(arg.args[0]) == Mul for arg in args):
            def f(arg):
                if type(arg) == Pow and type(arg.args[0]) == Mul:
                    return Pow(*arg.args, split = True)
                else:
                    return arg
            return Mul(*map(f, args))
        # Combine like terms
        elif nlogn_search(list(map(remove_exponent, args))):
            d = dict()
            for arg in args:
                if type(arg) == Pow:
                    arg = Pow(*arg.args, split = True)
                    if (p := arg.args[0]) in d:
                        d[p] += arg.args[1]
                    else:
                        d[p] = arg.args[1]
                else:
                    if arg in d:
                        d[arg] += 1
                    else:
                        d[arg] = 1
            return Mul(*[(k if d[k] == 1 else Pow(k, d[k])) for k in d])
        # Sort exponents in descending order
        elif list(args) != (s := sorted(args, key = lambda arg: float('inf') if is_constant(arg) else sign(get_exponent(arg)), reverse = True)):
            return Mul(*s)
        else:
            new = super(Mul, cls).__new__(cls)
            new.args = args
            return new

    def __repr__(self):
        def f(arg):
            if type(arg) in [Add, Pow]:
                return f'({arg})'
            else:
                return repr(arg)
        if self.args[0] == -1:
            return '-' + ' * '.join(map(f, self.args[1:]))
        else:
            return ' * '.join(map(f, self.args))

    # Manipulation

    def expand(self):
        if any(map(lambda x: type(x) == Add, self.args)):
            list_terms = lambda expr: (expr, ) if type(expr) != Add else expr.args
            return Add(Mul(*terms) for terms in list_mul(*map(list_terms, self.args)))
        else:
            return self

#####################
    # Conjugate #
#####################

class Conjugate(Expression):
    def __new__(cls, *args, distribute = False):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            if is_real(args[0]):
                return args[0]
            elif type(args[0]) == Infinity:
                return Infinity(Conjugate(args[0].c), args[0].deg)
            else:
                return complex(args[0].real, -args[0].imag)
        # Reverse conjugate
        elif type(args[0]) == Conjugate:
            return args[0].args[0]
        # Distribute conjugates
        elif distribute and type(args[0]) != Symbol:
            return type(args[0])(*[Conjugate(arg, distribute = True) for arg in args[0].args])
        else:
            new = super(Conjugate, cls).__new__(cls)
            new.args = args
            return new
    
    # Manipulation

    def expand(self):
        return Conjugate(*self.args, distribute = True)

###########################
    # Pow / Exp / Log #
###########################

class Pow(Expression):
    def __new__(cls, *args, split = False):
        assert len(args) == 2
        # If both base and exponent are constant return value
        if is_constant(args[0]) and is_constant(args[1]):
            base, exp = integerize(args[0]), integerize(args[1])
            return base ** exp
        # If exponent is 1 return original expression
        elif is_constant(args[1]) and abs(args[1] - 1) < 10 ** -10:
            return args[0]
        # If exponent is 0 return 1
        elif is_constant(args[1]) and abs(args[1]) < 10 ** -10:
            return 1
        # If base is 0 or 1 return base
        elif is_constant(args[0]) and integerize(args[0]) in [0, 1]:
            return integerize(args[0])
        # Convert e base to Exp
        elif (is_constant(args[0]) and abs(cpx_round(cmath.log(args[0])) - cmath.log(args[0])) < 10 ** -10):
            return Exp(cpx_round(cmath.log(args[0])) * args[1])
        # Convert Exp base to Exp
        elif type(args[0]) == Exp:
            return Exp(args[0].args[0] * args[1])
        # Convert near integer exponents to integer
        elif type(args[1]) == float and abs(round(args[1]) - args[1]) < 10 ** -10:
            return Pow(args[0], round(args[1]), split = split)
        # If base is Pow type combine exponents
        elif type(args[0]) == Pow:
            return Pow(args[0].args[0], args[0].args[1] * args[1], split = split)
        # Factor out constants
        elif type(args[0]) == Mul and is_constant(args[0].args[0]) and is_constant(args[1]):
            return (args[0].args[0] ** args[1]) * Pow(Mul(*args[0].args[1:]), args[1])
        # Split Mul into separate factors
        elif type(args[0]) == Mul and split:
            return Mul(*map(lambda arg: Pow(arg, args[1]), args[0].args))
        else:
            new = super(Pow, cls).__new__(cls)
            new.args = args
            return new

    def __repr__(self):
        if type(self.args[1]) in [float, int] and self.args[1] < 0:
            inverse = 1 / self
            return f'1 / {inverse}' if type(inverse) == Symbol else f'1 / ({inverse})'
        else:
            return f'{self.args[0]} ** {self.args[1]}' if type(self.args[0]) == Symbol else f'({self.args[0]}) ** {self.args[1]}'

    # Manipulation

    def expand(self):
        if type(self.args[0]) == Add and type(self.args[1]) == int:
            list_terms = lambda expr: (expr, ) if type(expr) != Add else expr.args
            if self.args[1] > 0:
                return Add(Mul(*terms) for terms in list_mul(*[list_terms(self.args[0])] * self.args[1]))
            else:
                return 1 / Add(Mul(*terms) for terms in list_mul(*[list_terms(self.args[0])] * -self.args[1]))
        else:
            return self

class Exp(Expression):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.exp(args[0])
        # If argument is type Log cancel Log
        elif type(args[0]) == Log:
            return args[0].args[0]
        else:
            new = super(Exp, cls).__new__(cls)
            new.args = args
            return new

class Log(Expression):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.log(args[0])
        # If argument is type Exp cancel Exp
        elif type(args[0]) == Exp:
            return args[0].args[0]
        # If argument is type Pow factor out exponent
        elif type(args[0]) == Pow:
            return Mul(args[0].args[1], Log(args[0].args[0]))
        # Factor out gcd of Mul exponents
        elif type(args[0]) == Mul and (cd := gcd(*map(get_exponent, args[0].args))) != 1:
            return cd * Log(Mul(*map(lambda arg: Pow(arg, 1 / cd), args[0].args)))
        else:
            new = super(Log, cls).__new__(cls)
            new.args = args
            return new

###############
    # Abs #
###############

class Abs(Expression):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return abs(args[0])
        # Flatten Abs
        if type(args[0]) == Abs:
            return args[0]
        # Adjust to sign positive
        elif sign(args[0]) == -1:
            return Abs(-args[0])
        else:
            new = super(Abs, cls).__new__(cls)
            new.args = args
            return new

class Trig(Expression):
    pass

class InvTrig(Expression):
    pass

###################################
    # Trigonometric Functions #
###################################

class Sin(Trig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.sin(args[0])
        # Cancel Asin
        elif type(args[0]) == Asin:
            return args[0].args[0]
        # Cancel Acos
        elif type(args[0]) == Acos:
            return Pow(1 - Pow(args[0].args[0], 2), Rational.half)
        # Cancel Atan
        elif type(args[0]) == Atan:
            arg = args[0].args[0]
            return arg / Pow(Pow(arg, 2) + 1, Rational.half)
        # Cancel multiple of InvTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvTrig):
            n, term = args[0].args
            sin, cos = Sin(term), Cos(term)
            return Add(*[((-1) ** r * binom(n, 2 * r + 1)) * Mul(Pow(cos, n - 2 * r - 1), Pow(sin, 2 * r + 1)) for r in range(math.ceil(n / 2))])
        # Cancel sum of InvTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvTrig) for arg in args[0].args]):
            return Sin(args[0].args[0]) * Cos(Add(*args[0].args[1:])) + Cos(args[0].args[0]) * Sin(Add(*args[0].args[1:]))
        else:
            new = super(Sin, cls).__new__(cls)
            new.args = args
            return new

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            sin, cos = Sin(term), Cos(term)
            return Add(*[((-1) ** r * binom(n, 2 * r + 1)) * Mul(Pow(cos, n - 2 * r - 1), Pow(sin, 2 * r + 1)) for r in range(math.ceil(n / 2))])
        elif type(args) == Add:
            return Sin(args.args[0]) * Cos(Add(*args.args[1:])) + Cos(args.args[0]) * Sin(Add(*args.args[1:]))
        else:
            return self

class Cos(Trig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.cos(args[0])
        # Cancel Asin
        elif type(args[0]) == Asin:
            return Pow(1 - Pow(args[0].args[0], 2), Rational.half)
        # Cancel Acos
        elif type(args[0]) == Acos:
            return args[0].args[0]
        # Cancel Atan
        elif type(args[0]) == Atan:
            return 1 / Pow(Pow(args[0].args[0], 2) + 1, Rational.half)
        # Cancel multiple of InvTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvTrig):
            n, term = args[0].args
            sin, cos = Sin(term), Cos(term)
            return Add(*[((-1) ** r * binom(n, 2 * r)) * Mul(Pow(cos, n - 2 * r), Pow(sin, 2 * r)) for r in range(math.ceil((n + 1) / 2))])
        # Cancel sum of InvTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvTrig) for arg in args[0].args]):
            return Cos(args[0].args[0]) * Cos(Add(*args[0].args[1:])) - Sin(args[0].args[0]) * Sin(Add(*args[0].args[1:]))
        else:
            new = super(Cos, cls).__new__(cls)
            new.args = args
            return new

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            sin, cos = Sin(term), Cos(term)
            return Add(*[((-1) ** r * binom(n, 2 * r)) * Mul(Pow(cos, n - 2 * r), Pow(sin, 2 * r)) for r in range(math.ceil((n + 1) / 2))])
        elif type(args) == Add:
            return Cos(args.args[0]) * Cos(Add(*args.args[1:])) - Sin(args.args[0]) * Sin(Add(*args.args[1:]))
        else:
            return self

class Tan(Trig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.tan(args[0])
        # Cancel Asin
        elif type(args[0]) == Asin:
            arg = args[0].args[0]
            return arg / Pow(1 - Pow(arg, 2), Rational.half)
        # Cancel Acos
        elif type(args[0]) == Acos:
            arg = args[0].args[0]
            return Pow(1 - Pow(arg, 2), Rational.half) / arg
        # Cancel Atan
        elif type(args[0]) == Atan:
            return args[0].args[0]
        # Cancel multiple of InvTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvTrig):
            n, term = args[0].args
            if type(term) in [Asin, Acos]:
                return Sin(args[0]) / Cos(args[0])
            else:
                tan = term.args[0]
                num = Add(*[((-1) ** r * binom(n, 2 * r + 1)) * Pow(tan, 2 * r + 1) for r in range(math.ceil(n / 2))])
                den = Add(*[((-1) ** r * binom(n, 2 * r)) * Pow(tan, 2 * r) for r in range(math.ceil((n + 1) / 2))])
                return num / den
        # Cancel sum of InvTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvTrig) for arg in args[0].args]):
            first, second = Tan(args[0].args[0]), Tan(Add(*args[0].args[1:]))
            return first * second / (1 - first * second)
        else:
            new = super(Cos, cls).__new__(cls)
            new.args = args
            return new 

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            tan = term.args[0]
            num = Add(*[((-1) ** r * binom(n, 2 * r + 1)) * Pow(tan, 2 * r + 1) for r in range(math.ceil(n / 2))])
            den = Add(*[((-1) ** r * binom(n, 2 * r)) * Pow(tan, 2 * r) for r in range(math.ceil((n + 1) / 2))])
            return num / den
        elif type(args) == Add:
            first, second = Tan(args.args[0]), Tan(Add(*args.args[1:]))
            return first * second / (1 - first * second)
        else:
            return self

###########################################
    # Inverse Trigonometric Functions #
###########################################

class Asin(InvTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.asin(args[0])
        else:
            new = super(Asin, cls).__new__(cls)
            new.args = args
            return new

class Acos(InvTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.acos(args[0])
        else:
            new = super(Acos, cls).__new__(cls)
            new.args = args
            return new

class Atan(InvTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return cmath.atan(args[0])
        else:
            new = super(Atan, cls).__new__(cls)
            new.args = args
            return new

class HTrig(Expression):
    pass

class InvHTrig(Expression):
    pass

##############################################
    # Hyperbolic Trigonometric Functions #
##############################################

class Sinh(HTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.sinh(args[0]))
        # Cancel Asinh
        elif type(args[0]) == Asinh:
            return args[0].args[0]
        # Cancel Acosh
        elif type(args[0]) == Acosh:
            return Pow(Add(-1, Pow(args[0].args[0], 2)), Rational.half)
        # Cancel Atanh
        elif type(args[0]) == Atanh:
            k = args[0].args[0]
            return Mul(k, Pow(Add(1, Mul(-1, Pow(k, 2))), Rational(-1, 2)))
        # Cancel multiple of InvHTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvHTrig):
            n, term = args[0].args
            sinh, cosh = Sinh(term), Cosh(term)
            return Add(*[binom(n, 2 * r + 1) * Mul(Pow(cosh, n - 2 * r - 1), Pow(sinh, 2 * r + 1)) for r in range(math.ceil(n / 2))])
        # Cancel sum of InvHTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvHTrig) for arg in args[0].args]):
            return Sinh(args[0].args[0]) * Cosh(Add(*args[0].args[1:])) + Cosh(args[0].args[0]) * Sinh(Add(*args[0].args[1:]))
        else:
            new = super(Sinh, cls).__new__(cls)
            new.args = args
            return new

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            sinh, cosh = Sinh(term), Cosh(term)
            return Add(*[binom(n, 2 * r + 1) * Mul(Pow(cosh, n - 2 * r - 1), Pow(sinh, 2 * r + 1)) for r in range(math.ceil(n / 2))])
        elif type(args) == Add:
            return Sinh(args.args[0]) * Cosh(Add(*args.args[1:])) + Cosh(args.args[0]) * Sinh(Add(*args.args[1:]))
        else:
            return self

class Cosh(HTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.sinh(args[0]))
        # Cancel Asinh
        elif type(args[0]) == Asinh:
            return Pow(Add(1, Pow(args[0].args[0], 2)), Rational.half)
        # Cancel Acosh
        elif type(args[0]) == Acosh:
            return args[0].args[0]
        # Cancel Atanh
        elif type(args[0]) == Atanh:
            k = args[0].args[0]
            return Pow(Add(1, Mul(-1, Pow(k, 2))), Rational(-1, 2))
        # Cancel multiple of InvHTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvHTrig):
            n, term = args[0].args
            sinh, cosh = Sinh(term), Cosh(term)
            return Add(*[binom(n, 2 * r) * Mul(Pow(cosh, n - 2 * r), Pow(sinh, 2 * r)) for r in range(math.ceil((n + 1) / 2))])
        # Cancel sum of InvHTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvHTrig) for arg in args[0].args]):
            return Cosh(args[0].args[0]) * Cosh(Add(*args[0].args[1:])) - Sinh(args[0].args[0]) * Sinh(Add(*args[0].args[1:]))
        else:
            new = super(Cosh, cls).__new__(cls)
            new.args = args
            return new

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            sinh, cosh = Sinh(term), Cosh(term)
            return Add(*[binom(n, 2 * r) * Mul(Pow(cosh, n - 2 * r), Pow(sinh, 2 * r)) for r in range(math.ceil((n + 1) / 2))])
        elif type(args[0]) == Add:
            return Cosh(args.args[0]) * Cosh(Add(*args.args[1:])) - Sinh(args.args[0]) * Sinh(Add(*args.args[1:]))
        else:
            return self

class Tanh(HTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.tanh(args[0]))
        # Cancel Asinh
        elif type(args[0]) == Asinh:
            k = args[0].args[0]
            return Mul(k, Pow(Add(1, Pow(k, 2)), Rational(-1, 2)))
        # Cancel Acosh
        elif type(args[0]) == Acosh:
            k = args[0].args[0]
            return Mul(Pow(Add(-1, Pow(k, 2)), Rational.half), Pow(k, -1))
        # Cancel Atanh
        elif type(args[0]) == Atanh:
            return args[0].args[0]
        # Cancel multiple of InvHTrig
        elif type(args[0]) == Mul and len(args[0].args) == 2 and type(args[0].args[0]) == int and isinstance(args[0].args[1], InvHTrig):
            n, term = args[0].args
            if type(term) in [Asinh, Acosh]:
                return Sinh(args[0]) / Cosh(args[0])
            else:
                tanh = term.args[0]
                num = Add(*[binom(n, 2 * r + 1) * Pow(tanh, 2 * r + 1) for r in range(math.ceil(n / 2))])
                den = Add(*[binom(n, 2 * r) * Pow(tanh, 2 * r) for r in range(math.ceil((n + 1) / 2))])
                return num / den
        # Cancel sum of InvHTrig
        elif type(args[0]) == Add and all([is_mul_of(arg, InvHTrig) for arg in args[0].args]):
            first, second = Tanh(args[0].args[0]), Tanh(Add(*args[0].args[1:]))
            return first * second / (1 - first * second)
        else:
            new = super(Tanh, cls).__new__(cls)
            new.args = args
            return new

    # Manipulation

    def expand(self):
        args = self.args[0]
        if type(args) == Mul and len(args.args) == 2 and type(args.args[0]) == int:
            n, term = args.args
            tanh = term.args[0]
            num = Add(*[binom(n, 2 * r + 1) * Pow(tanh, 2 * r + 1) for r in range(math.ceil(n / 2))])
            den = Add(*[binom(n, 2 * r) * Pow(tanh, 2 * r) for r in range(math.ceil((n + 1) / 2))])
            return num / den
        elif type(args) == Add:
            first, second = Tanh(args.args[0]), Tanh(Add(*args.args[1:]))
            return first * second / (1 - first * second)
        else:
            return self

######################################################
    # Inverse Hyperbolic Trigonometric Functions #
######################################################

class Asinh(InvHTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.asinh(args[0]))
        # Cancel Sinh
        elif type(args[0]) == Sinh:
            return args[0].args[0]
        else:
            new = super(Asinh, cls).__new__(cls)
            new.args = args
            return new

class Acosh(InvHTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.acosh(args[0]))
        # Cancel Cosh
        elif type(args[0]) == Cosh:
            return args[0].args[0]
        else:
            new = super(Acosh, cls).__new__(cls)
            new.args = args
            return new

class Atanh(InvHTrig):
    def __new__(cls, *args):
        assert len(args) == 1
        # If argument is constant return value
        if is_constant(args[0]):
            return integerize(cmath.atanh(args[0]))
        # Cancel Tanh
        elif type(args[0]) == Tanh:
            return args[0].args[0]
        else:
            new = super(Atanh, cls).__new__(cls)
            new.args = args
            return new


#####################
    # Equations #
#####################

