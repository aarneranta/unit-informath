#!/usr/bin/env python3
"""Aligning the proofs of an informal text with the steps of formal proofs.

Used by scripts/proof_sample.py -text-auto=<file.tex>.  For a declaration
named N in Unit:

* its text: the lemma whose title names it, \\begin{lemma}[..., \\nm{N}],
  and the proof after it; or the item (\\nm{N}) of a lemma's list, and the
  paragraph "(k)" of the lemma's proof, k the item's number;
* its fragments: each formula $...$ with the words before it; a chain of
  relations  $c = bk = (ah)k$  is cut at its relation symbols;
* the steps of each fragment: the steps whose conclusion it states.  The
  formulas of the text and the conclusions of the steps are terms of the
  same kind: | and = relations, products (juxtaposition, \\cdot), sums,
  negation, gcd, 0 and 1.  A piece of a chain states the relations that
  end at its operand (= a(hk) after c = bk = (ah)k states (ah)k = a(hk),
  bk = a(hk) and c = a(hk)); a mixture of = and | is |.  An equation
  matches either way round.  In a conclusion, the witness of a proof h,
  pi_1(h), is h, as texts name a quotient after its proof; a letter of the
  text that is not a variable of the theorem (a quotient q) matches any
  term.  A formula that is a term, not a relation ("the quotient is hk"),
  matches the steps that have it as an argument; a name (\\nm{div-scale},
  Lemma~\\ref{lem:M}) matches the steps that apply it.
"""

import re

import importlib.util
import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('informal_view', os.path.join(HERE, 'informal_view.py'))
iv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(iv)

# ---------------------------------------------------------------- the text

REFS = {}       # the number of a lemma -> its \\nm names (from find_text)


def labels(tex):
    """\\label{x} -> the \\nm{..} names of the environment it is in."""
    out = {}
    for m in re.finditer(r'\\begin\{(lemma|theorem|corollary|definition)\}(\[[^\]]*\])?(.*?)\\end\{\1\}', tex, re.S):
        names = re.findall(r'\\nm\{([^}]*)\}', m.group(2) or '')
        for l in re.findall(r'\\label\{([^}]*)\}', m.group(3)):
            out[l] = names
    return out


def clean(s, refs):
    s = re.sub(r'\\label\{[^}]*\}|\\qedhere', '', s)
    s = re.sub(r'Lemma~\\ref\{([^}]*)\}', lambda m: 'Lemma %s' % refs.get(m.group(1), ('?', []))[0], s)
    for l, (num, names) in refs.items():
        REFS[num] = names
    s = re.sub(r'~', ' ', s)
    s = re.sub(r'\\(begin|end)\{(itemize|enumerate)\}', '', s)
    return re.sub(r'\s+', ' ', s).strip()


def module_region(tex, module):
    """The text of a module's proof: from its mention (module \\nm{M}, or a
    lemma named after it) to the end of the proof it is in, without the
    items of the modules mentioned inside it; and where it starts."""
    m = re.search(r'module \\nm\{%s\}' % re.escape(module), tex) or \
        re.search(r'\\begin\{(lemma|theorem)\}\[[^\]]*\\nm\{%s\}' % re.escape(module), tex)
    if not m:
        return None, None
    end = tex.find('\\end{proof}', m.end())
    region = tex[m.end():end if end >= 0 else len(tex)]
    # a module inside: from its mention to the end of its list
    region = re.sub(r'module \\nm\{(?!%s\})[^}]*\}.*?\\end\{itemize\}' % re.escape(module), '', region, flags=re.S)
    return region, m.start()


def enclosing_lemma(tex, pos, numbers):
    """The number and page of the lemma whose proof a position is in."""
    best = None
    for m in re.finditer(r'\\begin\{(lemma|theorem|corollary)\}(\[[^\]]*\])?(.*?)\\end\{\1\}', tex, re.S):
        if m.start() < pos:
            best = m
    if best is None:
        return '?', '?'
    lab = re.search(r'\\label\{([^}]*)\}', best.group(3))
    return numbers.get(lab.group(1), ('?', '?')) if lab else ('?', '?')


def find_text(tex, qname, numbers):
    """(where, statement, proof) of the declaration with the qualified name
    qname, or None; numbers: label -> (number, page) of the compiled text.
    A member of a module (Tail.eq) is an item (\\nm{eq}) of its module's
    proof: its text is the proof."""
    refs = {l: (numbers.get(l, ('?', '?'))[0], ns) for l, ns in labels(tex).items()}
    parts = qname.split('.')
    name = parts[-1]
    nm = r'\\nm\{%s\}' % re.escape(name)
    # a lemma named after it
    for m in re.finditer(r'\\begin\{(lemma|theorem|corollary)\}\[([^\]]*)\](.*?)\\end\{\1\}', tex, re.S):
        if re.search(nm, m.group(2)):
            lab = re.search(r'\\label\{([^}]*)\}', m.group(3))
            num, page = numbers.get(lab.group(1), ('?', '?')) if lab else ('?', '?')
            pr = re.match(r'\s*\\begin\{proof\}(.*?)\\end\{proof\}', tex[m.end():], re.S)
            return ('%s %s, p. %s' % (m.group(1).capitalize(), num, page), clean(m.group(3), refs),
                    clean(pr.group(1), refs) if pr else '')
    # an item of a lemma's list
    for m in re.finditer(r'\\begin\{(lemma|theorem|corollary)\}(\[[^\]]*\])?(.*?)\\end\{\1\}', tex, re.S):
        items = re.split(r'\\item\s*', m.group(3))[1:]
        for k, it in enumerate(items, 1):
            head = re.match(r'\(([^)]*)\)', it)
            if head and re.search(nm, head.group(1)):
                lab = re.search(r'\\label\{([^}]*)\}', m.group(3))
                num, page = numbers.get(lab.group(1), ('?', '?')) if lab else ('?', '?')
                pr = re.match(r'\s*\\begin\{proof\}(.*?)\\end\{proof\}', tex[m.end():], re.S)
                proof = ''
                if pr:
                    p = re.search(r'\(%d\)(.*?)(?=\(\d+\)|$)' % k, pr.group(1), re.S)
                    proof = clean('(%d)' % k + p.group(1), refs) if p else ''
                return ('%s %s (%d), p. %s' % (m.group(1).capitalize(), num, k, page),
                        clean(it.replace('\\end{enumerate}', ''), refs), proof)
    # else a member of a module: an item of its module's proof
    if len(parts) >= 2:
        region, start = module_region(tex, parts[-2])
        if region:
            it = re.search(r'\\item\s*\(%s\)(.*?)(?=\\item|\\end\{(?:itemize|enumerate)\}|$)' % nm, region, re.S)
            if it:
                num, page = enclosing_lemma(tex, start, numbers)
                return ('Lemma %s, proof (module %s), item %s, p. %s' % (num, parts[-2], name, page), '',
                        clean(it.group(1), refs))
    return None


# claims in words between formulas, read as relations: (words, relation,
# number of formulas); the text's phrasings, as the symbol table's entries
# (Common, Prim) have them
VERBAL = [(r'is a common divisor of', 'common', 2), (r'is primitive', 'prim', 1)]
CLAIMS = []       # the claims of the text: (display, relation, its formulas)


def verbal(text):
    """$X$ is a common divisor of $Y$ as one formula $\\CLAIMk$, kept in
    CLAIMS with what it says."""
    for words, rel, k in VERBAL:
        pat = r'\$([^$]*)\$\s+' + words + (r'\s+\$([^$]*)\$' if k == 2 else '')
        def one(m):
            CLAIMS.append((m.group(0), rel, m.groups()))
            return '$\\CLAIM%d$' % (len(CLAIMS) - 1)
        text = re.sub(pat, one, text)
    return text


def fragments(text):
    """The fragments of a text: (words, math piece, math, index); a chain
    of relations is cut at its relation symbols.  The words before a
    formula up to the end of a clause (. , ; or a closing bracket) belong
    to the fragment before, and so do the words after the last formula."""
    out, words = [], ''
    for part in re.split(r'(\$[^$]*\$)', verbal(text)):
        if not part.startswith('$'):
            m = re.match(r'^(.*[.,;)])(\s.*)$', part, re.S) if out else None
            if m:
                w, p0, m0, i0 = out[-1]
                out[-1] = (w, p0, m0, i0, m.group(1)) if len(out[-1]) == 4 else out[-1]
                part = m.group(2)
            words += part
            continue
        math = part[1:-1]
        pieces = split_relations(math)
        for i, piece in enumerate(pieces):
            out.append((words if i == 0 else '', piece, math, i))
            words = ''
    if words.strip():
        if out and not re.search(r'\\nm|Lemma', words) and len(out[-1]) == 4:
            w, p0, m0, i0 = out[-1]
            out[-1] = (w, p0, m0, i0, words)
        else:
            out.append((words, None, None, None))
    return [f if len(f) == 5 else f + ('',) for f in out]


REL = r'(=|\\mid)'


def split_relations(math):
    """c = bk = (ah)k -> ['c = bk', '= (ah)k']: the first piece with its two
    operands, the others each a relation symbol and an operand (at the top
    level: not inside brackets)."""
    parts, depth, cur, i = [], 0, '', 0
    while i < len(math):
        ch = math[i]
        depth += {'(': 1, ')': -1, '{': 1, '}': -1}.get(ch, 0)
        m = re.match(REL, math[i:]) if depth == 0 else None
        if m:
            parts.append(cur)
            parts.append(m.group(1))
            cur, i = '', i + len(m.group(1))
            continue
        cur += ch
        i += 1
    parts.append(cur)
    if len(parts) < 5:
        return [math]
    out = ['%s %s %s' % (parts[0].strip(), parts[1], parts[2].strip())]
    for k in range(3, len(parts), 2):
        out.append('%s %s' % (parts[k], parts[k + 1].strip()))
    return out


# ---------------------------------------------------------------- formulas as terms

class TexParser:
    """$...$ of the text: relations, sums, products, atoms."""

    def __init__(self, s):
        s = s.replace('\\gcdd', ' gcd ').replace('\\operatorname{gcd}', ' gcd ').replace('\\cdot', ' * ')
        s = s.replace('\\mid', ' | ').replace('\\,', ' ').replace('\\cont', ' cont ').replace('\\mathrm{c}', ' cont ')
        # p_0 is the variable p0
        s = re.sub(r'([A-Za-z])_(\d)', r'\1\2', s)
        s = re.sub(r'([A-Za-z])_\{(\d)\}', r'\1\2', s)
        self.t = re.findall(r'gcd|cont|[A-Za-z]\d?|\d|[()=|+\-*,_{}]', s)
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self):
        self.i += 1
        return self.t[self.i - 1]

    def chain(self):
        """operands and relation symbols"""
        ops, rels = [self.sum()], []
        while self.peek() in ('=', '|'):
            rels.append(self.eat())
            ops.append(self.sum())
        return ops, rels

    def sum(self):
        if self.peek() == '-':
            self.eat()
            e = ('-', self.prod())
        else:
            e = self.prod()
        while self.peek() in ('+', '-'):
            op = self.eat()
            r = self.prod()
            e = ('+', e, r if op == '+' else ('-', r))
        return e

    def prod(self):
        e = self.atom()
        while self.peek() is not None and (self.peek() in ('*', '(', 'gcd', 'cont', '{') or
                                           re.match(r'[A-Za-z\d]', self.peek())):
            if self.peek() == '*':
                self.eat()
            e = ('*', e, self.atom())
        return e

    def atom(self):
        """an atom with its subscripts: p_i, (pq)_{i+1} are coefficients"""
        e = self.atom0()
        while self.peek() == '_':
            self.eat()
            if self.peek() == '{':
                self.eat()
                i = self.sum()
                if self.peek() == '}':
                    self.eat()
            else:
                i = self.atom0()
            e = ('coef', e, i)
        return e

    def atom0(self):
        t = self.peek()
        if t is None:
            raise SyntaxError('end')
        self.eat()
        if t == '(':
            ops, rels = self.chain()
            if self.peek() == ')':
                self.eat()
            return ops[0]
        if t == 'cont' and self.peek() == '(':
            self.eat()
            a = self.sum()
            if self.peek() == ')':
                self.eat()
            return ('c', a)
        if t == 'gcd':
            if self.peek() == '(':
                self.eat()
                a = self.sum()
                if self.peek() == ',':
                    self.eat()
                b = self.sum()
                if self.peek() == ')':
                    self.eat()
                return ('gcd', a, b)
            raise SyntaxError('gcd')
        if t.isdigit():
            return ('n', t)
        if re.match(r'[A-Za-z]', t):
            return ('v', t)
        if t == '{':
            e = self.sum()
            if self.peek() == '}':
                self.eat()
            return e
        raise SyntaxError(t)


def tex_relations(math, idx):
    """The relations that piece idx of a chain states (rel, x, y), or the
    term if the formula is not a relation: piece 0 the first relation,
    piece i the relations that end at operand i + 1."""
    try:
        ops, rels = TexParser(math).chain()
    except (SyntaxError, IndexError):
        return [], None
    if not rels:
        return [], ops[0]
    end = min(1 if idx == 0 else idx + 1, len(ops) - 1)
    return [('|' if '|' in rels[j:end] else '=', ops[j], ops[end]) for j in range(end)], None


LOCAL = set()     # the names of the local definitions met (x, y, t): not wildcards

SIMPLE = {'mul': '*', 'pmul': '*', 'add': '+', 'addP': '+'}


def norm(e):
    """A Dedukti term of the view as a term of the text's kind."""
    if isinstance(e, iv.Var):
        n = e.name
        return ('v', n)
    if isinstance(e, iv.Lam) or isinstance(e, iv.Pi):
        return ('?', iv.show(e))
    h, args = iv.spine(e)
    if isinstance(h, iv.Var):
        n = h.name
        if n == 'Proof' and args:
            return norm(args[0])
        # there is q with y = x q: x | y, Div unfolded
        if n == 'exists' and len(args) == 2 and isinstance(args[1], iv.Lam):
            q = args[1].name
            b = norm(args[1].body)
            if b[0] == '=' and b[2][0] == '*' and b[2][2] == ('v', q):
                return ('|', b[2][1], b[1])
        if n == 'Id' and len(args) == 3:
            return ('=', norm(args[1]), norm(args[2]))
        if n == 'peq' and len(args) >= 2:
            return ('=', norm(args[-2]), norm(args[-1]))
        if n.endswith('Common') and len(args) >= 2:
            return ('common', norm(args[-2]), norm(args[-1]))
        if n.endswith('Prim') and args and isinstance(args[-1], iv.Lam):
            b = norm(args[-1].body)
            if b[0] == 'coef':
                return ('prim', b[1])
        # for all i, x divides the i-th coefficient of f: x is a common divisor of f
        if n == 'forall' and len(args) == 2 and isinstance(args[1], iv.Lam):
            i = args[1].name
            c = norm(args[1].body)
            if c[0] == '|' and c[2][0] == 'coef' and c[2][2] == ('v', i):
                return ('common', c[1], c[2][1])
        if n == 'Div' and len(args) >= 2:
            return ('|', norm(args[-2]), norm(args[-1]))
        if n in SIMPLE and len(args) >= 2:
            return (SIMPLE[n], norm(args[-2]), norm(args[-1]))
        if n == 'neg' and args:
            return ('-', norm(args[-1]))
        if n == 'Ring_Nat_zero':
            return ('n', '0')
        if n == 'z':
            return ('n', '0')
        if n == 'o':
            return ('n', '1')
        if n.endswith('gcd') and len(args) >= 2:
            return ('gcd', norm(args[-2]), norm(args[-1]))
        if n in ('fst', 'andEl') and args:
            return norm(args[-1])
        # polynomials: a + Xp, coefficients, contents, X p, scalars
        if n == 'cons' and len(args) == 3:
            return ('+', norm(args[1]), ('*', ('v', 'X'), norm(args[2])))
        if n == 'shift' and args:
            return ('*', ('v', 'X'), norm(args[-1]))
        if n == 'scal' and len(args) >= 2:
            return ('*', norm(args[-2]), norm(args[-1]))
        if n.endswith('coef') and len(args) >= 2:
            return ('coef', norm(args[-2]), norm(args[-1]))
        if n == 'Ring_Nat_suc' and args:
            return ('+', norm(args[-1]), ('n', '1'))
        if n == 'Ring_Nat_zero':
            return ('n', '0')
        if n.endswith('content') and args:
            return ('c', norm(args[-1]))
        # a local definition of a module at its parameters (x, y of Tail,
        # t of One): the text names it so
        last = n.split('_')[-1]
        if args and all(isinstance(a, iv.Var) for a in args) and len(last) <= 2 and last.islower():
            LOCAL.add(last)
            return ('v', last)
        # a local definition at other arguments (t of One at a, p, g): its value there
        if n in DEFTERMS and len(args) == len(DEFTERMS[n][0]):
            ps, body = DEFTERMS[n]
            return norm(iv.subst_vars(body, dict(zip(ps, args))))
    return ('app', iv.show(e))


DEFS = {}         # a local definition's name -> its value (set by the caller)
DEFTERMS = {}     # a local definition (its constant) -> its parameters and value (set by the caller)


def match(t, f, vars_, sub):
    """Whether the text's term t is the formal term f; a letter of t that is
    not a variable of the theorem matches any term, the same one wherever
    it occurs; the name of a local definition matches its value too."""
    if t[0] == 'v' and t[1] in DEFS and f != t and match(DEFS[t[1]], f, vars_, sub):
        return True
    if t[0] == 'v' and t[1] not in vars_:
        if t[1] in sub:
            return sub[t[1]] == f
        sub[t[1]] = f
        return True
    if t[0] != f[0] or len(t) != len(f):
        return False
    if t[0] in ('v', 'n'):
        return t[1] == f[1]
    return all(match(a, b, vars_, sub) for a, b in zip(t[1:], f[1:]))


def rel_matches(r, concl, vars_):
    rel, x, y = r
    if not isinstance(concl, tuple) or concl[0] != rel:
        return False
    # an equation of polynomials, stated by their coefficients
    if rel == '=' and concl[1][0] == 'coef' and concl[2][0] == 'coef' and concl[1][2] == concl[2][2] and \
            x[0] != 'coef' and rel_matches(r, ('=', concl[1][1], concl[2][1]), vars_):
        return True
    if match(x, concl[1], vars_, {}) and match(y, concl[2], vars_, {}) and \
            (lambda s: match(x, concl[1], vars_, s) and match(y, concl[2], vars_, s))({}):
        return True
    return rel == '=' and (lambda s: match(x, concl[2], vars_, s) and match(y, concl[1], vars_, s))({})


def subterms(t, acc):
    acc.append(t)
    if t[0] not in ('v', 'n', 'app', '?'):
        for a in t[1:]:
            subterms(a, acc)
    return acc


def align(text, steps, vars_):
    """Fragments of a text with the numbers of their steps.
    steps: number -> (conclusion as a term, rule name, data arguments as terms)."""
    out = []
    for words, piece, math, idx, after in fragments(text):
        hit = set()
        names = re.findall(r'\\nm\{([^}]*)\}', words + after)
        names += [n for num in re.findall(r'Lemma ([\d.]+)', words) for n in REFS.get(num, [])]
        for n in names:
            n2 = re.sub(r'[-.]', '_', n.split(',')[0].strip())
            hit |= {k for k, (_, rule, _) in steps.items() if rule and (rule == n2 or rule.endswith('_' + n2))}
        claim = re.match(r'\\CLAIM(\d+)$', piece or '')
        if claim:
            disp, rel, forms = CLAIMS[int(claim.group(1))]
            try:
                terms = [TexParser(f).sum() for f in forms]
                hit |= {k for k, (c, _, _) in steps.items()
                        if isinstance(c, tuple) and c[0] == rel and len(c) == len(terms) + 1 and
                        (lambda s: all(match(t, f, vars_, s) for t, f in zip(terms, c[1:])))({})}
            except (SyntaxError, IndexError):
                pass
            out.append([words + disp + after, sorted(hit)])
            continue
        if piece is not None and not re.search(r'\bwith\s*$', words):
            rels, term = tex_relations(math, idx)
            for r in rels:
                hit |= {k for k, (c, _, _) in steps.items() if rel_matches(r, c, vars_)}
            if term is not None and term[0] not in ('v', 'n'):
                hit |= {k for k, (_, _, data) in steps.items() if any(match(term, d, vars_, {}) for d in data)}
        text_piece = words + ('$%s$' % piece if piece is not None else '') + after
        out.append([text_piece, sorted(hit)])
    return out
