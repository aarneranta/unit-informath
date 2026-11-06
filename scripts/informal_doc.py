#!/usr/bin/env python3
"""The informal document of a Unit development: its declarations read by
Informath, one section per segment, each section saying its parameters once.

    python3 scripts/informal_doc.py out/gcddomain.dk out/gcddomain.dkgf gcddomain-view.dkgf out/gcddomain-doc.tex

The declarations are those of scripts/informal_view.py (the informal view of
unit2dk's output).  unit2dk lifts the parameters of a segment into every
member; the #STRUCTURE lines of its .dkgf say which they are.  Here a member
is read without the parameters of the segments it is in, and each segment
gets a section whose first sentence says its own parameters, as an informal
text does: "In this section, let A be a commutative ring and G a gcd domain
on A."  The context sentence is Informath's reading of the parameters as the
hypotheses of a statement, without its conclusion.

RunInformath is called twice: with -json for the readings, and with
-to-latex-doc for the LaTeX macros of the symbol table.
"""

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

CTX = 'SectionContext'      # the conclusion of the context statements, cut off
PREAMBLE = r"""\documentclass{article}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsmath}
\setlength\parindent{0pt}
\setlength\parskip{8pt}
\title{%s}
\date{}
\begin{document}
\maketitle
\newcommand{\meets}{\mathrel{\supset\!\!\!\subset}}
\newcommand{\notmeets}{\mathrel{\not\meets}}
"""


def runinformath():
    root = os.environ.get('INFORMATH_ROOT', '')
    import glob
    built = glob.glob(os.path.join(root, '.stack-work', 'dist', '*', '*', 'build', 'RunInformath', 'RunInformath'))
    return max(built, key=os.path.getmtime) if built else 'RunInformath'


def structures(dkgf):
    """#STRUCTURE lines: segment -> (its own parameters, its members), in order."""
    segs = {}
    for l in open(dkgf):
        m = re.match(r'#STRUCTURE (\S+) \((.*?)\) ?(.*)$', l.strip())
        if m:
            segs[m.group(1)] = (m.group(2).split(), m.group(3).split())
    return segs


def escape_text(s):
    """Underscores outside math as \\_ (labels such as div_trans)."""
    out, math, i = [], False, 0
    while i < len(s):
        c = s[i]
        if c == '\\' and i + 1 < len(s):
            out.append(s[i:i + 2])
            i += 2
            continue
        if c == '$':
            math = not math
        out.append('\\_' if c == '_' and not math else c)
        i += 1
    return ''.join(out)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if len(args) != 4:
        sys.exit(__doc__)
    dk, dkgf, table, out = args
    text = open(dk).read()
    text = text[text.index('(; the program ;)'):] if '(; the program ;)' in text else text
    decls = iv.judgements(text)
    view = iv.View(decls, iv.records(dkgf))
    segs = structures(dkgf)
    seg_of = {m: s for s, (_, ms) in segs.items() for m in ms}

    def segment(n):
        if n in seg_of:
            return seg_of[n]
        cands = [s for s in segs if n.startswith('{|' + s + '.')]
        return max(cands, key=len) if cands else None

    def chain(s):
        """The segments s is in, outermost first, and s."""
        return sorted([p for p in segs if s == p or s.startswith(p + '.')], key=len) if s else []

    def params(ss):
        return [x for p in ss for x in segs[p][0] if x not in iv.BACKGROUND]

    # the constants of the symbol table keep their parameters: their entries
    # count them (#2 is the second argument), and Informath reads the
    # declaration of a constant as its definiendum applied to its binders
    entries = {l.split(':')[0].strip() for l in open(table) if ':' in l and not l.startswith('(;')}
    consts0 = sorted({n for _, n, _, _ in decls if n and n.startswith('{|')} | set(view.recs))
    short0 = iv.short_names(consts0)
    # the declarations, without their sections' parameters
    items, firsts = [], {}
    for kw, n, t, b in decls:
        if n is None or kw == 'other':
            continue
        s = segment(n)
        keep = iv.quote(short0.get(n, n)) in entries
        try:
            d = view.declaration(kw, n, t, b, strip=() if keep else params(chain(s)))
        except (SyntaxError, IndexError, RecursionError) as e:
            d = None
        if d:
            items.append((s, n, d))
            firsts.setdefault(s, (n, t))
    # the context of each section: its own parameters, from the type of its
    # first declaration
    contexts = {}
    for k, (s, (n, t)) in enumerate(firsts.items()):
        own = [x for x in segs.get(s, ([], []))[0] if x not in iv.BACKGROUND]
        if not own:
            continue
        outer = params(chain(s)[:-1])
        bs = view.binders(t)
        # past the outer parameters, the own ones in order
        i = 0
        for x in outer:
            if i < len(bs) and bs[i][0] == x:
                i += 1
        mine = []
        for x in own:
            if i < len(bs) and bs[i][0] == x:
                mine.append(bs[i])
                i += 1
        if not mine:
            continue
        ty = iv.App(iv.Var('Proof'), iv.Var(CTX))
        for x, a in reversed(mine):
            ty = iv.Pi(x, a, ty)
        contexts[s] = ('Ctx%d' % k, '%s : %s.' % ('Ctx%d' % k, iv.show(ty)))
    # one file for Informath, with the short names of the view
    body = '\n\n'.join([c for _, c in contexts.values()] + [d for _, _, d in items])
    consts = sorted({n for _, n, _, _ in decls if n and n.startswith('{|')} | set(view.recs))
    short = iv.short_names(consts)
    body = re.sub(r'\{\|[^|]*\|\}', lambda m: iv.quote(short[m.group(0)]) if m.group(0) in short else m.group(0), body)
    body = iv.unprime(body, set())
    run = runinformath()
    with tempfile.TemporaryDirectory() as tmp:
        f = os.path.join(tmp, 'doc.dk')
        open(f, 'w').write(body + '\n')
        r = subprocess.run([run, '-json', '-no-back-to-dedukti', '-languages=Eng', '-add-symboltables=' + table, f],
                           capture_output=True, text=True)
        readings = {}
        for l in r.stdout.split('\n'):
            if not l.strip().startswith('{'):
                continue
            j = json.loads(l)
            ws = j['originalDedukti'].split()
            name = ws[1] if ws[0] == 'def' else ws[0]
            ranks = j['nlgResults'].get('InformathEng')
            if ranks:
                readings[name] = ranks[0]['lin']
        r = subprocess.run([run, '-to-latex-doc', '-to-lang=Eng', '-add-symboltables=' + table, f],
                           capture_output=True, text=True)
        macros = [l for l in r.stdout.split('\n') if l.startswith('\\newcommand') and
                  'meets' not in l]

    def name_of(d):
        ws = d.split()
        return ws[1] if ws[0] == 'def' else ws[0]

    def short_of(n):
        return iv.unprime(iv.quote(short.get(n, n)), set())
    lines, current, missing = [], None, []
    for s, n, d in items:
        if s != current:
            current = s
            title = (s or 'Top level').replace('Theory.', '')
            lines.append('\\%s{%s}' % ('section' if '.' not in title else 'subsection', escape_text(title)))
            if s in contexts:
                c = readings.get(contexts[s][0], '')
                c = re.sub(r'^\S+\.\s+', '', c, count=1)
                cut = c.rfind(' Then ')
                if cut >= 0:
                    c = c[:cut]
                if c:
                    lines.append('\\emph{In this section:} ' + escape_text(c))
        dn = re.sub(r'\{\|[^|]*\|\}', lambda m: short_of(m.group(0)), n)
        rd = readings.get(short_of(n)) or readings.get(name_of(re.sub(r'\{\|[^|]*\|\}', lambda m: short_of(m.group(0)), d)))
        if rd:
            lines.append(escape_text(rd))
        else:
            missing.append(n)
    title = os.path.basename(dk)[:-3]
    open(out, 'w').write((PREAMBLE % escape_text(title)) + '\n'.join(macros) + '\n\n' + '\n\n'.join(lines) +
                         '\n\\end{document}\n')
    print('%d declarations in %d sections, %d read, %d without a reading -> %s'
          % (len(items), len({s for s, _, _ in items}), len(items) - len(missing), len(missing), out))
    if missing:
        print('without a reading: ' + ' '.join(short_of(n) for n in missing))


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    main()
