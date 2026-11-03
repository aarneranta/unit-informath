"""Check a translated .dk file with dk, declaration by declaration: at each
error, the declaration is demoted (a definition to an axiom of its type, a
set of rules dropped, a declaration whose type fails removed) and the check
starts again.  Reports how many declarations dk accepts and the demoted
ones, with the first line of their error.

    python3 scripts/dkcheck_all.py out/core.dk [-max=N]   # -> out/core.checked.dk, out/core.demoted.txt
"""
import re, subprocess, sys

def check(path):
    r = subprocess.run(['dk', 'check', '--eta', path], capture_output=True, text=True)
    out = re.sub(r'\x1b\[[0-9;]*m', '', r.stdout + r.stderr)
    m = re.search(r'\[line:(\d+) column:(\d+)\]', out)
    return (int(m.group(1)), out) if r.returncode and m else (None, out)

def main():
    src = sys.argv[1]
    limit = int(next((a[5:] for a in sys.argv if a.startswith('-max=')), 100000))
    lines = open(src, encoding='utf-8').read().split('\n')
    base = src[:-3]
    tmp = base + '.checked.dk'
    demoted = []
    for _ in range(limit):
        open(tmp, 'w', encoding='utf-8').write('\n'.join(lines))
        line, out = check(tmp)
        if line is None:
            break
        i = line - 1
        text = lines[i]
        why = ' '.join(out.split('\n')[1:3]).strip()[:200]
        name = (re.match(r'(?:def )?(\S+)', text) or re.match('', '')).group(0)
        if text.startswith('def ') and ' := ' in text:
            lines[i] = text[4:text.index(' := ')] + ' .'          # an axiom of its type
            demoted.append((name, 'definition -> axiom', why))
        elif text.startswith('['):
            lines[i] = '(; rules dropped ;)'
            demoted.append((name, 'rules dropped', why))
        else:
            lines[i] = '(; declaration removed ;)'
            demoted.append((name, 'removed', why))
    decls = sum(1 for l in lines if re.match(r'(def )?\{\|', l))
    rules = sum(1 for l in lines if l.startswith('['))
    with open(base + '.demoted.txt', 'w', encoding='utf-8') as f:
        for n, k, w in demoted:
            f.write('%s\t%s\t%s\n' % (n, k, w))
    print('%s: %d declarations and %d rule sets accepted by dk; %d demoted (%s.demoted.txt)'
          % (src, decls, rules, len(demoted), base))

main()
