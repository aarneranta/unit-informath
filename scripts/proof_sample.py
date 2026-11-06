#!/usr/bin/env python3
"""A page of proofs of a Unit development: the Unit source, the step-by-step
Unit and Dedukti terms, Informath's proof text, and the proof in the
original informal text, linked by the numbers of the proof text.

    python3 scripts/proof_sample.py out/gcddomain.dk out/gcddomain.dkgf gcddomain-view.dkgf \\
        ../unit/sag/gcddomain out/proofs.html Theory.GcdDomain.Divisibility.div-refl ...

The proofs are those of scripts/informal_view.py -proofs (the informal view,
with unit-nd.dk as the rules of exists, and, transport); RunInformath
-proof-text -proof-text-dedukti -force-symbolic writes their texts.  A proof
text numbers the hypotheses first and then the steps in post-order, each step
after its premisses; the steps of the proof term are numbered the same way
here (checked against the rules of the text's lines), and each is shown as
its rule applied to its other arguments, with the numbers of its premisses
in place of their proofs, indented by its depth in the proof:

    9   Ring_trans (R A) c ... [3] [8]          trans 3 8
    3     snd (R A) (q => ...) k                k.2

In the Unit column, the steps are written in Unit's notation: the arguments
that Unit leaves implicit ({x y : A} in the declaration) and the parameters
of the segments a constant is in are not shown, a projection is p.1, p.2, a
pair (a, p).  Hovering over a row highlights it; a premiss's number links to
its row.

With -text=proof-sample.json, each proof also has its statement and proof in
the original text (unit/doc/gcddomain.tex), in fragments, each with the
steps it says: hovering over a fragment highlights its steps, and over a
step the fragments that say it.  The alignment is made by hand.  With
-text-auto=gcddomain.tex instead, the text and its alignment are found by
scripts/align.py (and written to <out>-alignment.json).  The Dedukti column
is hidden until its check box is ticked.
"""

import html
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('informal_view', os.path.join(HERE, 'informal_view.py'))
iv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(iv)
Var, App, Lam, Pi = iv.Var, iv.App, iv.Lam, iv.Pi
ROOT = os.path.dirname(HERE)
spec2 = importlib.util.spec_from_file_location('align', os.path.join(HERE, 'align.py'))
align = importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(align)
align.iv = iv          # one module of terms, for isinstance
MATHJAX = 'https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js'


def runinformath():
    import glob
    root = os.environ.get('INFORMATH_ROOT', '')
    built = glob.glob(os.path.join(root, '.stack-work', 'dist', '*', '*', 'build', 'RunInformath', 'RunInformath'))
    return max(built, key=os.path.getmtime) if built else 'RunInformath'


# ---------------------------------------------------------------- Unit's declarations

def unit_decl(segdir, qname):
    """The source of a declaration (qualified name) in its .seg file, and its
    binders [(name, implicit)]: the first line at which the name begins a
    declaration, and the lines after it that are indented more or continue it."""
    parts = qname.split('.')
    files = [parts[1] if parts[0] == 'Theory' else parts[0]]
    name = parts[-1]
    for f in files:
        path = os.path.join(segdir, f + '.seg')
        if not os.path.exists(path):
            continue
        lines = open(path).read().split('\n')
        for i, l in enumerate(lines):
            m = re.match(r'^(\s*)%s(\s|$)' % re.escape(name), l)
            if not m or l.strip().startswith('--'):
                continue
            ind = len(m.group(1))
            out = [l]
            for l2 in lines[i + 1:]:
                if l2.strip() and (len(l2) - len(l2.lstrip())) <= ind and not l2.strip().startswith(('}', ')')):
                    break
                out.append(l2)
            while out and not out[-1].strip():
                out.pop()
            return '\n'.join(out), binders(l[m.end():])
    return None, []


def binders(s):
    """The binders after a declaration's name: (x y : A) {z : B} ..."""
    out, i = [], 0
    while True:
        while i < len(s) and s[i] == ' ':
            i += 1
        if i >= len(s) or s[i] not in '({':
            return out
        close = ')' if s[i] == '(' else '}'
        depth, j = 0, i
        while j < len(s):
            depth += {'(': 1, '{': 1, ')': -1, '}': -1}.get(s[j], 0)
            if depth == 0:
                break
            j += 1
        inner = s[i + 1:j]
        names = inner.split(':')[0].split()
        out += [(x, close == '}') for x in names]
        i = j + 1


# ---------------------------------------------------------------- proof steps

def result_is_proof(t):
    while isinstance(t, Pi):
        t = t.body
    h, _ = iv.spine(t)
    return isinstance(h, Var) and h.name in ('Proof', 'Prop') and h.name == 'Proof'


def proof_positions(t):
    """The argument positions of a constant that are proofs."""
    out, k = [], 0
    while isinstance(t, Pi):
        h, _ = iv.spine(t.typ)
        if isinstance(h, Var) and h.name == 'Proof':
            out.append(k)
        elif isinstance(t.typ, Pi) and result_is_proof(t.typ):
            out.append(k)
        k, t = k + 1, t.body
    return out


class Steps:
    """The steps of a proof term, numbered as -proof-text numbers its lines."""

    def __init__(self, types, hyps):
        self.types = types           # constant -> its type (base)
        self.num = dict(hyps)        # hypothesis -> its number
        self.n = len(hyps)
        self.steps = []              # (number, term, depth, premisses)
        self.seen = {}

    def walk(self, e, depth=0):
        """The number of the line that proves e."""
        if isinstance(e, Var) and e.name in self.num:
            return self.num[e.name]
        key = iv.show(e)
        if key in self.seen:
            return self.seen[key]
        h, args = iv.spine(e)
        prem = {}
        if isinstance(h, Var) and h.name in self.types:
            for k in proof_positions(self.types[h.name]):
                if k < len(args):
                    prem[k] = self.walk(args[k], depth + 1)
        self.n += 1
        self.seen[key] = self.n
        self.steps.append((self.n, e, depth, prem))
        return self.n


# ---------------------------------------------------------------- printing

def dk_step(e, prem):
    h, args = iv.spine(e)
    return ' '.join([iv.show(h, 1)] + ['[%d]' % prem[k] if k in prem else iv.show(a, 2) for k, a in enumerate(args)])


class UnitPrinter:
    """Terms of the view in Unit's notation."""

    def __init__(self, long_of, segdir, segparams, sels):
        self.long_of, self.segdir, self.segparams, self.sels = long_of, segdir, segparams, sels
        self.cache = {}

    def implicit(self, name):
        """The positions of the arguments of a constant that Unit does not show."""
        if name in self.cache:
            return self.cache[name]
        q = self.long_of.get(name)
        hidden = set()
        if q:
            q0 = q[2:-2]
            k = self.segparams(q)
            hidden = set(range(k))
            if q in self.sels:
                hidden = set(range(k + 1))          # the record element: the record is opened
            _, bs = unit_decl(self.segdir, q0)
            base = max(hidden) + 1 if hidden else 0
            hidden |= {base + i for i, (_, imp) in enumerate(bs) if imp}
        self.cache[name] = hidden
        return hidden

    def name(self, n):
        q = self.long_of.get(n)
        return q[2:-2].split('.')[-1] if q else n

    def show(self, e, prem=None, prec=0):
        prem = prem or {}
        if isinstance(e, Var):
            return self.name(e.name)
        if isinstance(e, Lam):
            s = '\\ %s -> %s' % (e.name, self.show(e.body))
            return '(%s)' % s if prec else s
        if isinstance(e, Pi):
            return iv.show(e, 2 if prec else 0)
        h, args = iv.spine(e)
        ref = lambda k, a: '%d' % prem[k] if k in prem else self.show(a, None, 2)
        if isinstance(h, Var):
            n = h.name
            if n in ('fst', 'snd') and len(args) == 3:
                return '%s.%s' % (ref(2, args[2]), '1' if n == 'fst' else '2')
            if n in ('andEl', 'andEr') and len(args) == 3:
                return '%s.%s' % (ref(2, args[2]), '1' if n == 'andEl' else '2')
            if n == 'existsI' and len(args) == 4:
                return '(%s, %s)' % (self.show(args[2]), ref(3, args[3]))
            if n == 'andI' and len(args) == 4:
                return '(%s, %s)' % (ref(2, args[2]), ref(3, args[3]))
            if n == 'refl' and len(args) == 2:
                s = 'refl %s' % self.show(args[1], None, 2)
                return '(%s)' % s if prec > 1 else s
            if n == 'Id' and len(args) == 3:
                return 'Id %s %s %s' % tuple(self.show(a, None, 2) for a in args)
            hidden = self.implicit(n)
            shown = [ref(k, a) for k, a in enumerate(args) if k not in hidden]
            if not shown:
                return self.name(n)
            s = ' '.join([self.name(n)] + shown)
            return '(%s)' % s if prec > 1 else s
        s = ' '.join([self.show(h, None, 2)] + [self.show(a, None, 2) for a in args])
        return '(%s)' % s if prec > 1 else s


# ---------------------------------------------------------------- the proof texts

def tables(section):
    out = []
    for t in re.findall(r'\\begin\{tabular\}\{[^\n]*\}\n(.*?)\\end\{tabular\}', section, re.S):
        out.append([[c.strip() for c in r.split('&')] for r in t.split('\\\\') if '&' in r])
    return out


def macros_of(lines):
    """\\newcommand lines as MathJax macros."""
    out = {}
    for l in lines:
        m = re.match(r'\\newcommand\{\\(\w+)\}(?:\[(\d+)\])?\{(.*)\}\s*$', l.strip())
        if m:
            out[m.group(1)] = [m.group(3), int(m.group(2))] if m.group(2) else m.group(3)
    return out


def text_html(s):
    """A sentence of a proof text: LaTeX text, math left to MathJax."""
    s = s.replace('\\hspace*{1.5em}', '')
    s = re.sub(r'\\texttt\{(.*?)\}', lambda m: '<code>%s</code>' % m.group(1).replace('\\_', '_'), s)
    return s


STYLE = """
body{font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;max-width:1400px;margin:1.5rem auto;padding:0 16px;color:#1d1d1f;line-height:1.45}
h1{font-size:1.5rem} h2{font-size:1.2rem;margin-top:2.5rem;border-bottom:2px solid #3a6ea5;padding-bottom:.2rem}
.lab{color:#666;font-size:.75rem;text-transform:uppercase;letter-spacing:.04em;margin:.8rem 0 .2rem}
pre{background:#f6f8fa;border:1px solid #e1e4e8;border-radius:6px;padding:.5rem .7rem;overflow:auto;font-size:.82rem;margin:0}
pre.unit{background:#fbf8ef;border-color:#ece3c8}
table.steps{border-collapse:collapse;width:100%;font-size:.88rem}
table.steps th{text-align:left;font-weight:600;color:#555;border-bottom:1px solid #ccc;padding:.3rem .4rem;font-size:.78rem}
table.steps td{vertical-align:top;padding:.25rem .4rem;border-bottom:1px solid #eee}
table.steps tr:hover td,table.steps tr:target td{background:#fff4c2}
td.num{text-align:right;color:#3a6ea5;font-weight:600;white-space:nowrap}
td.code{font-family:ui-monospace,Menlo,monospace;font-size:.78rem;white-space:pre-wrap;word-break:break-word}
td.unit{background:#fbf8ef}
.dk{display:none} body.show-dk .dk{display:table-cell}
.orig{border-left:3px solid #3d8b37;background:#f3faf2;padding:.4rem .7rem;margin:.3rem 0;border-radius:0 6px 6px 0}
.orig .where{color:#3d8b37;font-size:.8rem;margin-bottom:.2rem}
.frag{border-radius:3px;cursor:default}
.frag[data-steps]:hover,.frag.hl{background:#fff1a8}
table.steps tr.hl td{background:#fff4c2}
.toggle{font-size:.88rem;color:#555;margin:.5rem 0}
td.just code{color:#6a4c93}
a.ref{color:#3a6ea5;text-decoration:none;font-weight:600}
details{margin-top:.5rem} summary{cursor:pointer;color:#3a6ea5;font-size:.85rem}
.stmt{margin:.3rem 0}
"""


# the macros of gcddomain.tex that its fragments use
TEXT_MACROS = {'gcdd': '\\operatorname{gcd}', 'cont': '\\mathrm{c}'}


def orig_html(frags, anchor):
    """Fragments of the original text, each with the steps it says."""
    out = []
    for t, steps in frags:
        t = html.escape(t)
        t = re.sub(r'\\nm\{(.*?)\}', r'<code>\1</code>', t)
        attr = ' data-steps="%s"' % ' '.join(anchor(k) for k in steps) if steps else ''
        out.append('<span class="frag"%s>%s</span>' % (attr, t))
    return ''.join(out)


SCRIPT = """
document.addEventListener('DOMContentLoaded', function () {
  var box = document.getElementById('show-dk');
  box.addEventListener('change', function () { document.body.classList.toggle('show-dk', box.checked); });
  function rowsOf(f) { return (f.dataset.steps || '').split(' ').filter(Boolean).map(function (i) { return document.getElementById(i); }); }
  document.querySelectorAll('.frag[data-steps]').forEach(function (f) {
    f.addEventListener('mouseenter', function () { rowsOf(f).forEach(function (r) { r && r.classList.add('hl'); }); });
    f.addEventListener('mouseleave', function () { rowsOf(f).forEach(function (r) { r && r.classList.remove('hl'); }); });
  });
  document.querySelectorAll('table.steps tr[id]').forEach(function (r) {
    var fs = Array.prototype.filter.call(document.querySelectorAll('.frag[data-steps]'), function (f) {
      return f.dataset.steps.split(' ').indexOf(r.id) >= 0; });
    r.addEventListener('mouseenter', function () { fs.forEach(function (f) { f.classList.add('hl'); }); });
    r.addEventListener('mouseleave', function () { fs.forEach(function (f) { f.classList.remove('hl'); }); });
  });
});
"""


def tex_numbers(tex):
    """label -> (number, page), from compiling a copy of the text."""
    d = tempfile.mkdtemp()
    f = os.path.join(d, 'text.tex')
    open(f, 'w').write(open(tex).read())
    subprocess.run(['pdflatex', '-interaction=nonstopmode', 'text.tex'], cwd=d, capture_output=True)
    out = {}
    aux = os.path.join(d, 'text.aux')
    if os.path.exists(aux):
        for m in re.finditer(r'\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{([^}]*)\}', open(aux).read()):
            out[m.group(1)] = (m.group(2), m.group(3))
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if len(args) < 6:
        sys.exit(__doc__)
    dk, dkgf, table, segdir, out = args[:5]
    names = args[5:]
    texts, tex = {}, None
    for a in sys.argv[1:]:
        if a.startswith('-text='):
            texts = json.load(open(a[6:]))
        if a.startswith('-text-auto='):
            tex = a[11:]
    numbers = tex_numbers(tex) if tex else {}
    run = runinformath()
    tmp = tempfile.mkdtemp()
    # the view with the proofs, and the base of their rules and lemmas
    r = subprocess.run([sys.executable, os.path.join(HERE, 'informal_view.py'), dk, dkgf, '-proofs=' + ','.join(names)],
                       capture_output=True, text=True, check=True)
    base_txt, proofs_txt = r.stdout.split('(; PROOFS ;)')
    base = os.path.join(tmp, 'base.dk')
    open(base, 'w').write(open(os.path.join(ROOT, 'unit-nd.dk')).read() + '\n' + base_txt)
    pf = os.path.join(tmp, 'proofs.dk')
    open(pf, 'w').write(proofs_txt)
    r = subprocess.run([run, '-proof-text', '-proof-text-dedukti', '-force-symbolic', '-languages=Eng',
                        '-base=' + base, '-add-symboltables=' + table, pf], capture_output=True, text=True)
    secs = re.split(r'\\subsection\*', r.stdout)[1:]
    # the statements, read symbolically
    proofs = iv.judgements(proofs_txt)
    stmts = os.path.join(tmp, 'stmts.dk')
    open(stmts, 'w').write('\n\n'.join('%s : %s.' % (n, iv.show(t)) for _, n, t, _ in proofs) + '\n')
    r2 = subprocess.run([run, '-json', '-no-back-to-dedukti', '-force-symbolic', '-languages=Eng',
                         '-add-symboltables=' + table, stmts], capture_output=True, text=True)
    reading = {}
    for l in r2.stdout.split('\n'):
        if l.startswith('{'):
            j = json.loads(l)
            rk = j['nlgResults'].get('InformathEng')
            if rk:
                reading[j['originalDedukti'].split()[0]] = re.sub(r'^\S+\.\s+', '', rk[0]['lin'], count=1)
    r3 = subprocess.run([run, '-to-latex-doc', '-force-symbolic', '-to-lang=Eng', '-add-symboltables=' + table, stmts],
                        capture_output=True, text=True)
    macros = macros_of(r3.stdout.split('\n'))
    macros.update(TEXT_MACROS)
    # the types of the base, for the premisses of each rule
    types = {n: t for _, n, t, _ in iv.judgements(open(base).read()) if n}
    # Unit's names and segments
    text = open(dk).read()
    decls = iv.judgements(text[text.index('(; the program ;)'):])
    consts = sorted({n for _, n, _, _ in decls if n and n.startswith('{|')} | set(iv.records(dkgf)))
    short = iv.short_names(consts)
    long_of = {iv.quote(s): q for q, s in short.items()}
    segs = {}
    for l in open(dkgf):
        m = re.match(r'#STRUCTURE (\S+) \((.*?)\)', l)
        if m:
            segs[m.group(1)] = [x for x in m.group(2).split() if x not in iv.BACKGROUND]

    def segparams(q):
        q0 = q[2:-2]
        own = [s for s in segs if q0.startswith(s + '.')]
        # the parameters that stay in the view: not levels (a level is a
        # parameter whose name the view never binds; those of the segments
        # above the program's modules are levels: a, l)
        return sum(len([x for x in segs[s] if x not in ('a', 'l', 'k', 'j')]) for s in own)
    sels = {s for (_, ss) in iv.records(dkgf).values() for s in ss}
    up = UnitPrinter(long_of, segdir, segparams, sels)

    body = ['<h1>Proofs of sag/gcddomain: Unit, Dedukti and Informath</h1>',
            '<p>For each proof: its statement, read by Informath; the Unit source; and its steps, '
            'numbered as Informath\'s proof text numbers its lines (the hypotheses first, then each '
            'step after its premisses). In the Unit and Dedukti columns a step is its rule applied to '
            'its other arguments, with the numbers of its premisses in place of their proofs, and '
            'indented by its depth in the proof. Hover over a row to highlight it; a number links to '
            'the row of its step. The texts are made with <code>RunInformath -proof-text '
            '-proof-text-dedukti -force-symbolic</code>.</p>'
            '<p>Above each table, in green, the statement and proof in the original text '
            '(Coquand, <i>Gauss\'s lemma and polynomial gcd domains</i>, unit/doc/gcddomain.tex), '
            'cut in fragments: hovering over a fragment highlights the steps it says, and over a '
            'step the fragments that say it. This alignment is made by hand.</p>'
            '<div class="toggle"><label><input type="checkbox" id="show-dk"> show the Dedukti steps</label></div>']
    report, aligned = [], {}
    for (kw, n, t, b), sec in zip(proofs, secs):
        q = long_of[n][2:-2] if n in long_of else n
        src, _ = unit_decl(segdir, q)
        tbs = tables(sec)
        eng, dkt = (tbs + [[], []])[:2]
        # the hypotheses: the definiens' lambdas whose type is a proof
        hyps, tt, bb = [], t, b
        while isinstance(bb, Lam) and isinstance(tt, Pi):
            h, _ = iv.spine(tt.typ)
            if isinstance(h, Var) and h.name == 'Proof':
                hyps.append(bb.name)
            bb, tt = bb.body, tt.body
        st = Steps(types, [(x, i + 1) for i, x in enumerate(hyps)])
        st.walk(bb)
        # the steps against the text's lines: the rule of each
        rules = [re.sub(r'\\texttt\{(.*?)\}.*', r'\1', row[2]).replace('\\_', '_').strip() for row in dkt]
        ok = len(dkt) == len(hyps) + len(st.steps) and all(
            rules[num - 1] == iv.spine(e)[0].name for num, e, _, _ in st.steps if isinstance(iv.spine(e)[0], Var))
        report.append('%s: %d lines, %d hypotheses and %d steps%s' % (n, len(dkt), len(hyps), len(st.steps),
                                                                     '' if ok else ' (NOT ALIGNED)'))
        pid = re.sub(r'\W', '_', n)
        anchor = lambda k: '%s-%d' % (pid, k)
        link = lambda s: re.sub(r'\[(\d+)\]', lambda m: '<a class="ref" href="#%s">%s</a>' % (anchor(int(m.group(1))), m.group(1)), s)
        body.append('<h2 id="%s">%s</h2>' % (pid, html.escape(q.split('.')[-1])))
        body.append('<div class="stmt">%s</div>' % html.escape(reading.get(n, '')))
        orig = texts.get(q.split('.')[-1])
        if tex:
            found = align.find_text(open(tex).read(), q.split('.')[-1], numbers)
            if found:
                where, stm, prf = found
                # the steps: their conclusions (the Dedukti lines), rules and data arguments
                concl = {}
                for k, row in enumerate(dkt, 1):
                    m = re.match(r'\\verb#(?:[^#:]* : )?(.*)#$', row[1].replace('\\hspace*{1.5em}', ''))
                    try:
                        concl[k] = align.norm(iv.Parser(iv.tokens(m.group(1))).term()) if m else None
                    except (SyntaxError, IndexError):
                        concl[k] = None
                rule = {num: (iv.spine(e)[0].name if isinstance(iv.spine(e)[0], Var) else None)
                        for num, e, _, _ in st.steps}
                data = {num: [align.norm(a) for k2, a in enumerate(iv.spine(e)[1]) if k2 not in prem]
                        for num, e, _, prem in st.steps}
                steps = {k: (concl.get(k), rule.get(k), data.get(k, [])) for k in range(1, len(dkt) + 1)}
                vars_ = set()
                bb2 = b
                while isinstance(bb2, Lam):
                    vars_.add(bb2.name)
                    bb2 = bb2.body
                orig = {'where': where, 'statement': align.align(stm, steps, vars_),
                        'proof': align.align(prf, steps, vars_) if prf else [['(no proof in the text)', []]]}
                aligned[q.split('.')[-1]] = orig
        if orig:
            body.append('<div class="lab">The original text</div><div class="orig"><div class="where">%s</div>'
                        '<div><b>Statement.</b> %s</div><div><b>Proof.</b> %s</div></div>'
                        % (html.escape(orig['where']), orig_html(orig['statement'], anchor),
                           orig_html(orig['proof'], anchor)))
        body.append('<div class="lab">Unit source</div><pre class="unit">%s</pre>' % html.escape(src or '(not found)'))
        rows = {}
        for i, x in enumerate(hyps):
            rows[i + 1] = ('', html.escape(x), html.escape(x), 0)
        for num, e, depth, prem in st.steps:
            uni = up.show(e, {k: v for k, v in prem.items()})
            uni = re.sub(r'(?<![\w.])(\d+)(?![\w])', lambda m: '[%s]' % m.group(1) if int(m.group(1)) in prem.values() else m.group(1), uni)
            rows[num] = ('', link(html.escape(uni)), link(html.escape(dk_step(e, prem))), depth)
        tr = ['<table class="steps"><tr><th>#</th><th>Informath</th><th>by</th><th>Unit</th><th class="dk">Dedukti</th></tr>']
        for k, row in enumerate(eng, 1):
            num, sent, just = (row + ['', '', ''])[:3]
            _, u, d, depth = rows.get(k, ('', '', '', 0))
            ind = '&nbsp;' * 2 * depth if k > len(hyps) else ''
            just = re.sub(r'(\d+)', lambda m: '<a class="ref" href="#%s">%s</a>' % (anchor(int(m.group(1))), m.group(1)),
                          text_html(just))
            tr.append('<tr id="%s"><td class="num">%d</td><td>%s</td><td class="just">%s</td>'
                      '<td class="code unit">%s%s</td><td class="code dk">%s%s</td></tr>'
                      % (anchor(k), k, text_html(sent), just, ind, u, ind, d))
        tr.append('</table>')
        body.append('<div class="lab">Steps</div>' + '\n'.join(tr))
        body.append('<details><summary>the proof term in Dedukti (the informal view)</summary><pre>%s</pre></details>'
                    % html.escape(iv.show(b)))
    page = ('<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            '<title>Unit proofs</title><script>window.MathJax={tex:{inlineMath:[["$","$"]],macros:%s}};</script>'
            '<script async src="%s"></script><script>%s</script><style>%s</style></head><body>\n%s\n</body></html>\n'
            % (json.dumps(macros), MATHJAX, SCRIPT, STYLE, '\n'.join(body)))
    open(out, 'w').write(page)
    print('\n'.join(report))
    if tex:
        # the alignment made, for comparing or correcting
        json.dump(aligned, open(out[:-5] + '-alignment.json', 'w'), indent=1, ensure_ascii=False)
    print('-> %s' % out)


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    main()
