#!/usr/bin/env python3
"""The informal view of unit2dk's output: Dedukti in Informath's dialect.

    python3 scripts/informal_view.py out/gcddomain.dk out/gcddomain.dkgf > out/gcddomain-view.dk
    python3 scripts/informal_view.py out/gcddomain.dk out/gcddomain.dkgf -only=Theory.GcdDomain   # one module

unit2dk's output is type-correct Dedukti in an encoding of Unit (universe
levels, codes of types a la Tarski, lifts, the segments' parameters lifted
into every declaration).  Informath reads mathematics in its own dialect:
Set, Elem, Prop, Proof, forall, exists, if, and, not, false.  This script
rewrites the declarations of the program (not the prelude) into it:

* levels go: the binders of type Lvl, the level arguments of every constant
  and variable that takes them, lift, and the codes' level arguments;
* the parameters of the foundations (BACKGROUND: univ, images, surjections,
  the Theory segment's axioms, which the informal text assumes once and for
  all) go, with the arguments that give them;
* U l is Set, and El of a code is a type: of pi a function type, of id an
  equation  Proof (Id A x y), of a proposition  Proof P, of anything else
  Elem A;
* a proposition is a code that is an identity type, Empty, a Pi into a
  proposition (forall, if; not for P -> Empty), a sigma of a proposition
  (exists, and), or a constant defined as one of these;
* a record (the #RECORD lines of the .dkgf) is a structure: its constructor
  is declared  R : (fields) -> Structure,  and its type, selectors,
  variants with fixed fields and their coercions (.up) are not declared;
  a coercion is the identity;
* a definition of a type or a proposition keeps its definiens; any other
  definition (a theorem, a construction) is its statement only;
* definitions by rewrite rules (split) are left out.

Names: a constant is named by the shortest suffix of its qualified name
that no other constant has, with . and - as _ (div_trans, Gcd_gcd, ...).

The result is for reading, not for checking: dropping levels and the
foundations' parameters loses information that a type checker would need.
"""

import re
import sys

BACKGROUND = ['univ', 'images', 'surjections']
LEVEL_TYPE = 'Lvl'

# ---------------------------------------------------------------- terms


class Var:
    def __init__(self, name): self.name = name


class App:
    def __init__(self, fun, arg): self.fun, self.arg = fun, arg


class Lam:
    def __init__(self, name, typ, body): self.name, self.typ, self.body = name, typ, body


class Pi:
    def __init__(self, name, typ, body): self.name, self.typ, self.body = name, typ, body


TOKEN = re.compile(r'\(;.*?;\)|\{\|.*?\|\}|-->|->|=>|:=|[()\[\],.:]|[^\s()\[\],:.]+(?:\.[^\s()\[\],:.]+)*', re.S)
PUNCT = ('(', ')', '[', ']', ',', '.', ':', '->', '=>', '-->', ':=')


def tokens(text):
    return [t for t in TOKEN.findall(text) if not t.startswith('(;')]


class Parser:
    """Dedukti terms, as in Dedukti's own grammar."""

    def __init__(self, toks):
        self.toks, self.i = toks, 0

    def peek(self, k=0):
        return self.toks[self.i + k] if self.i + k < len(self.toks) else None

    def eat(self, t):
        if self.peek() != t:
            raise SyntaxError('expected %s, found %s' % (t, self.peek()))
        self.i += 1

    def ident(self, t):
        return t is not None and t not in PUNCT

    def term(self):
        t, t1 = self.peek(), self.peek(1)
        if self.ident(t) and t1 == ':':
            self.i += 2
            a = self.aterm()
            if self.peek() == '->':
                self.i += 1
                return Pi(t, a, self.term())
            self.eat('=>')
            return Lam(t, a, self.term())
        if self.ident(t) and t1 == '=>':
            self.i += 2
            return Lam(t, None, self.term())
        if t == '(' and self.ident(t1) and self.peek(2) == ':':
            save = self.i
            self.i += 3
            a = self.aterm()
            if self.peek() == ')' and self.peek(1) == '->':
                self.i += 2
                return Pi(t1, a, self.term())
            self.i = save
        a = self.aterm()
        if self.peek() == '->':
            self.i += 1
            return Pi(None, a, self.term())
        return a

    def aterm(self):
        f = self.sterm()
        while self.peek() == '(' or self.ident(self.peek()):
            f = App(f, self.sterm())
        return f

    def sterm(self):
        t = self.peek()
        if t == '(':
            self.i += 1
            e = self.term()
            self.eat(')')
            return e
        if not self.ident(t):
            raise SyntaxError('unexpected %s' % t)
        self.i += 1
        return Var(t)


def spine(e):
    args = []
    while isinstance(e, App):
        args.append(e.arg)
        e = e.fun
    return e, args[::-1]


def apps(f, args):
    for a in args:
        f = App(f, a)
    return f


def show(e, prec=0):
    if isinstance(e, Var):
        return e.name
    if isinstance(e, App):
        s = '%s %s' % (show(e.fun, 1), show(e.arg, 2))
        return '(%s)' % s if prec > 1 else s
    if isinstance(e, Lam):
        s = '%s%s => %s' % (e.name, ' : ' + show(e.typ, 1) if e.typ is not None else '', show(e.body))
    else:
        if e.name is None:
            s = '%s -> %s' % (show(e.typ, 1), show(e.body))
        else:
            s = '(%s : %s) -> %s' % (e.name, show(e.typ, 1), show(e.body))
    return '(%s)' % s if prec > 0 else s


def free(e, x):
    if isinstance(e, Var):
        return e.name == x
    if isinstance(e, App):
        return free(e.fun, x) or free(e.arg, x)
    if e.typ is not None and free(e.typ, x):
        return True
    return e.name != x and free(e.body, x)


# ---------------------------------------------------------------- the file

def judgements(text):
    """(keyword, name, type, body) of the declarations of a Dedukti text;
    rules and other judgements are ('rules', None, None, None)."""
    toks = tokens(text)
    out, i = [], 0
    while i < len(toks):
        j, depth = i, 0
        while j < len(toks) and not (toks[j] == '.' and depth == 0):
            depth += {'(': 1, ')': -1, '[': 1, ']': -1}.get(toks[j], 0)
            j += 1
        jm, i = toks[i:j], j + 1
        if not jm:
            continue
        kw = 'static'
        if jm[0] in ('def', 'thm', 'injective'):
            kw, jm = jm[0], jm[1:]
        if len(jm) < 3 or jm[1] != ':' or jm[0] in PUNCT:
            out.append(('other', None, None, None))
            continue
        p = Parser(jm[2:])
        typ = p.term()
        body = None
        if p.peek() == ':=':
            p.i += 1
            body = p.term()
        out.append((kw, jm[0], typ, body))
    return out


def records(dkgf):
    """#RECORD lines: record -> (constructor, selectors)."""
    out = {}
    for l in open(dkgf):
        w = l.split()
        if w and w[0] == '#RECORD':
            out[w[1]] = (w[2], w[3:])
    return out


class View:
    def __init__(self, decls, recs):
        self.recs = recs
        self.cons = {c: r for r, (c, _) in recs.items()}
        self.sels = {s for (_, ss) in recs.values() for s in ss}
        self.drop = {}      # constant -> the positions of its arguments that go
        self.props = set()  # constants that are propositions (types read as Prop)
        self.structs = set()
        for r in recs:
            self.structs.add(r)
        # the variants of records with fixed fields, and their coercions
        self.variants = {n for _, n, _, _ in decls if n and re.match(r'\{\|.*\[.*\]\|\}$', n)}
        self.ups = {n for _, n, _, _ in decls if n and re.match(r'\{\|.*\]\.up\|\}$', n)}
        for _, n, t, _ in decls:
            if n:
                self.drop[n] = self.dropped(t)

    def dropped(self, t):
        """The argument positions a type's binders give that go: levels and
        the background parameters (the variables of their types too)."""
        out, k = [], 0
        while isinstance(t, Pi):
            if self.goes(t.name, t.typ):
                out.append(k)
            k += 1
            t = t.body
        return out

    def goes(self, name, typ):
        if name in BACKGROUND:
            return True
        h, _ = spine(typ)
        return isinstance(h, Var) and h.name == LEVEL_TYPE

    # -- terms

    def term(self, e, env):
        """A term; env: the bound variables that go, and for those that stay
        the positions of their arguments that go."""
        if isinstance(e, Var):
            return e
        if isinstance(e, Lam):
            if e.typ is not None and self.goes(e.name, e.typ):
                return self.term(e.body, dict(env, **{e.name: None}))
            env2 = dict(env)
            env2[e.name] = self.dropped(e.typ) if e.typ is not None else []
            return Lam(e.name, self.type_(e.typ, env) if e.typ is not None else None, self.term(e.body, env2))
        if isinstance(e, Pi):
            return self.type_(e, env)
        h, args = spine(e)
        if isinstance(h, Var):
            name = h.name
            pos = env[name] if name in env else self.drop.get(name, [])
            if pos is None:
                return Var(name)      # a level variable, applied: cannot be
            args = [a for k, a in enumerate(args) if k not in pos]
            # the encoding's own constants
            if name == 'lift':
                return self.term(args[-1], env) if args else h
            if name in ('U', 'u'):
                return Var('Set')
            if name in self.ups:
                return self.term(args[-1], env)
            # a proposition as an argument (isProp (Not (id ..))): as one
            if name in ('pi', 'sigma', 'id') or name.endswith(('.Not|}', '.Plus|}')):
                p = self.prop(e, env)
                if p is not None:
                    return p
            args = [self.term(a, env) for a in args]
            if name in ('pi', 'sigma', 'id', 'pair', 'fst', 'snd', 'refl', 'J', 'El'):
                return apps(Var(name), args[self.levels(name):])
            return apps(h, args)
        return apps(self.term(h, env), [self.term(a, env) for a in args])

    def levels(self, c):
        """The level arguments of the prelude's constants (they are not in self.drop)."""
        return {'pi': 2, 'sigma': 2, 'id': 1, 'pair': 2, 'fst': 2, 'snd': 2, 'refl': 1, 'El': 1}.get(c, 0)

    # -- types and propositions

    def type_(self, t, env):
        """A type (of a declaration or a binder)."""
        if isinstance(t, Pi):
            if self.goes(t.name, t.typ):
                return self.type_(t.body, dict(env, **{t.name or '_': None}))
            env2 = dict(env)
            if t.name:
                env2[t.name] = self.dropped(t.typ)
            return Pi(t.name, self.type_(t.typ, env), self.type_(t.body, env2))
        h, args = spine(t)
        if isinstance(h, Var) and h.name == 'U':
            return Var('Set')
        if isinstance(h, Var) and h.name == 'El':
            return self.el(args[-1], env)
        return self.term(t, env)

    def el(self, code, env):
        """The type of the elements of a code."""
        h, args = spine(code)
        if isinstance(h, Var):
            if h.name == 'lift':
                return self.el(args[-1], env)
            if h.name == 'u':
                return Var('Set')
            if h.name == 'pi' and len(args) == 4 and isinstance(args[3], Lam):
                lam = args[3]
                env2 = dict(env, **{lam.name: []})
                return Pi(lam.name if free(lam.body, lam.name) else None, self.el(args[2], env),
                          self.el(lam.body, env2))
        p = self.prop(code, env)
        if p is not None:
            return App(Var('Proof'), p)
        return App(Var('Elem'), self.term(code, env))

    def prop(self, code, env):
        """A code as a proposition, or None if it is not one."""
        h, args = spine(code)
        if not isinstance(h, Var):
            return None
        n = h.name
        if n == 'lift':
            return self.prop(args[-1], env)
        if n == 'id' and len(args) == 4:
            a, x, y = (self.term(z, env) for z in args[1:])
            return apps(Var('Id'), [a, x, y])
        if n == 'Empty' or n.endswith('.Empty|}'):
            return Var('false')
        if n == 'pi' and len(args) == 4 and isinstance(args[3], Lam):
            lam = args[3]
            env2 = dict(env, **{lam.name: []})
            q = self.prop(lam.body, env2)
            if q is None:
                return None
            if isinstance(q, Var) and q.name == 'false':
                p = self.prop(args[2], env)
                if p is not None:
                    return App(Var('not'), p)
            p = self.prop(args[2], env)
            if p is not None and not free(lam.body, lam.name):
                return apps(Var('if'), [p, q])
            return apps(Var('forall'), [self.term(args[2], env), Lam(lam.name, None, q)])
        if n == 'sigma' and len(args) == 4 and isinstance(args[3], Lam):
            lam = args[3]
            env2 = dict(env, **{lam.name: []})
            q = self.prop(lam.body, env2)
            if q is None:
                return None
            p = self.prop(args[2], env)
            if p is not None and not free(lam.body, lam.name):
                return apps(Var('and'), [p, q])
            return apps(Var('exists'), [self.term(args[2], env), Lam(lam.name, None, q)])
        # not A, and A or B (the sum of two propositions: a decision)
        if n.endswith('.Not|}') and len(args) >= 1:
            p = self.prop(args[-1], env)
            return App(Var('not'), p) if p is not None else None
        if n.endswith('.Plus|}') and len(args) >= 2:
            p, q = self.prop(args[-2], env), self.prop(args[-1], env)
            return apps(Var('or'), [p, q]) if p is not None and q is not None else None
        if n in self.props:
            return self.term(code, env)
        return None

    # -- declarations

    def declaration(self, kw, n, t, b):
        if n in self.sels or n in self.variants or n in self.ups or n in self.structs:
            return None
        if n in self.cons:
            # a record: its constructor's fields as a structure
            r = self.cons[n]
            ty = self.type_(t, {})
            fields = []
            while isinstance(ty, Pi):
                fields.append((ty.name, ty.typ))
                ty = ty.body
            s = Var('Structure')
            for x, a in reversed(fields):
                s = Pi(x, a, s)
            return '%s : %s.' % (r, show(s))
        ty = self.type_(t, {})
        # the type's result: a type or a proposition gets its definiens
        res = ty
        while isinstance(res, Pi):
            res = res.body
        if b is not None and isinstance(res, Var) and res.name == 'Set':
            body, env = b, {}
            # the definiens' lambdas, as the type's binders
            names = []
            tt = t
            while isinstance(body, Lam) and isinstance(tt, Pi):
                if self.goes(tt.name, tt.typ):
                    env[body.name] = None
                else:
                    names.append(body.name)
                body, tt = body.body, tt.body
            p = self.prop(body, env)
            if p is not None:
                self.props.add(n)
                ty = self.retype(ty, Var('Prop'))
                d = p
            else:
                d = self.term(body, env)
            for x in reversed(names):
                d = Lam(x, None, d)
            return 'def %s : %s :=\n  %s.' % (n, show(ty), show(d))
        return '%s : %s.' % (n, show(ty))

    def retype(self, t, r):
        if isinstance(t, Pi):
            return Pi(t.name, t.typ, self.retype(t.body, r))
        return r


# the names unit2dk primes, as the prelude's (u'), which the view does not have
PRELUDE = {'Lvl', 'lz', 'ls', 'lmax', 'U', 'El', 'u', 'lift', 'pi', 'sigma', 'pair', 'fst', 'snd',
           'id', 'refl', 'J', 'one', 'tt'}


def short_names(names):
    """The shortest suffix of each qualified name that no other name has."""
    def parts(n):
        return n[2:-2].split('.') if n.startswith('{|') else [n]
    out = {}
    split = {n: parts(n) for n in names}
    for n, ps in split.items():
        for k in range(1, len(ps) + 1):
            s = '.'.join(ps[-k:])
            # not a name of the prelude, which the view gives back to the variables
            if s in PRELUDE:
                continue
            if sum(1 for m in split.values() if '.'.join(m[-k:]) == s) == 1:
                out[n] = s
                break
        else:
            out[n] = '.'.join(ps)
    return out


def unprime(body, constants):
    """u' as u, where the program has no constant u."""
    return re.sub(r"(?<![A-Za-z0-9_'])(%s)'(?![A-Za-z0-9_'])" % '|'.join(sorted(PRELUDE - constants)),
                  lambda m: m.group(1), body)


def quote(s):
    """A plain identifier (Informath looks up symbol table entries only for
    those): . and - as _, quoted only if that is not enough."""
    s = s.replace('.', '_').replace('-', '_')
    return s if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", s) else '{|%s|}' % s


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if len(args) < 2:
        sys.exit(__doc__)
    only = [a[6:] for a in sys.argv[1:] if a.startswith('-only=')]
    text = open(args[0]).read()
    text = text[text.index('(; the program ;)'):] if '(; the program ;)' in text else text
    decls = judgements(text)
    view = View(decls, records(args[1]))
    out = []
    for kw, n, t, b in decls:
        if n is None or kw == 'other':
            continue
        # -only=Prefix,..: the declarations of these modules only (all are viewed,
        # for the propositions they define)
        keep = not only or any(n.startswith('{|' + p) for o in only for p in o.split(','))
        try:
            d = view.declaration(kw, n, t, b)
        except (SyntaxError, IndexError, RecursionError) as e:
            d = '(; %s: not viewed (%s) ;)' % (n, e)
        if d and keep:
            out.append(d)
    body = '\n\n'.join(out)
    # shorter names: the qualified names of the program's constants
    consts = sorted({n for _, n, _, _ in decls if n and n.startswith('{|')} | set(view.recs))
    short = short_names(consts)
    body = re.sub(r'\{\|[^|]*\|\}', lambda m: quote(short[m.group(0)]) if m.group(0) in short else m.group(0), body)
    body = unprime(body, set())
    print('(; the informal view of %s, by scripts/informal_view.py ;)\n' % args[0])
    print(body)


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    main()
