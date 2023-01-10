import sys
sys.setrecursionlimit(10000)
print("Python Recursive Limitation = ", sys.getrecursionlimit())

# Testing first with S, K and I

i = lambda x : x
k = lambda x : lambda y : x
s = lambda x : lambda y : lambda z : x(z)(y(z))
print(s(k)(k)(17))

# This is the applicative order fixedpoint combinator Z

z = lambda f: (lambda x: f(lambda z: x(x)(z)))(lambda x: f(lambda z: x(x)(z)))
h = lambda f: lambda x: 1 if x==0 else x*f(x-1)
print(z(h)(6))

# However, on Klop's combinator I get maximum recursion depth exceeded

p = lambda a: lambda b: lambda c: lambda d: lambda e: lambda f: lambda g: lambda h: lambda i: lambda j: lambda k: lambda l: lambda m: lambda n: lambda o: lambda p: lambda q: lambda s: lambda t: lambda u: lambda v: lambda w: lambda x: lambda y: lambda z: lambda r: r(t(h)(i)(s)(i)(s)(a)(f)(i)(x)(e)(d)(p)(o)(i)(n)(t)(c)(o)(m)(b)(i)(n)(a)(t)(o)(r))
y = p(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)(p)
h = lambda f: lambda x: 1 if x==0 else x*f(x-1)
print(y(h)(6))


