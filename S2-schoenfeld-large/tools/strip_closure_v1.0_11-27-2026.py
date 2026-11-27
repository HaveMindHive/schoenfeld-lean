"""Declaration-level closure of the Schoenfeld chain in goldbach-lean, and the stripped port.
usage: python3 -I strip_closure_v1.0_11-27-2026.py SRC_ENTRY_DIR OUT_DIR  (prints the closure table)
Over-approximates: a name token resolves to every declaration it could mean in the imported files."""
import re, sys, os, collections
SRC, OUT = sys.argv[1], sys.argv[2]
TOPMOD = 'LeanLab.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge'
P = 'LeanLab.PNTPort.ExplicitPsi1.Trivial.'
TARGETS = [P + n for n in ['psi_schoenfeld_large', 'theta_schoenfeld_large', 'psi_sub_theta_large']]
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|notation|infix|infixl|infixr|prefix|postfix|macro|syntax|elab|macro_rules|elab_rules|irreducible_def|example)'
MOD = r'(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public|meta|scoped|local)\s+)*'
declre = re.compile(r'^' + MOD + KW + r'\b\s*([^\s:({\[]+)?')
NAMED = {'theorem', 'lemma', 'def', 'abbrev', 'structure', 'inductive', 'class', 'opaque', 'axiom', 'irreducible_def'}
prefre = re.compile(r'^(/--|@\[|(set_option|open|omit|include|variable|attribute|local|lemma_parse_unused)\s.*\sin\s*$)')


def path(m):
    return os.path.join(SRC, m.replace('.', '/') + '.lean')


imports, tc = {}, {}


def imp(m):
    if m not in imports:
        r = []
        for line in open(path(m)):
            mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)', line)
            if mm and mm.group(1).startswith('LeanLab'):
                r.append(mm.group(1))
        imports[m] = r
    return imports[m]


def trans(m):
    if m not in tc:
        s = {m}
        for i in imp(m):
            s |= trans(i)
        tc[m] = s
    return tc[m]


allm = trans(TOPMOD)
items, opens = {}, {}
for m in allm:
    L = open(path(m)).read().split('\n')
    starts = []
    ns = []
    op = set()
    pending = None
    incomment = False
    for k, line in enumerate(L):
        if incomment:
            if '-/' in line:
                incomment = False
            continue
        if not line or line[0] in ' \t)':
            continue
        mn = re.match(r'^namespace\s+(\S+)', line)
        me = re.match(r'^end\s+(\S+)', line)
        mo = re.match(r'^open\s+(?:scoped\s+)?([^(\n]*)', line)
        if mo:
            for o in mo.group(1).split():
                if o == 'in':
                    break
                parts = '.'.join(ns).split('.') if ns else []
                for j in range(len(parts) + 1):
                    op.add('.'.join(parts[:j] + [o]))
        d = declre.match(re.sub(r'^(@\[[^\]]*\]\s*)+', '', line))
        if d:
            kind = d.group(1)
            nm = d.group(2) if kind in NAMED else None
            if kind == 'example':
                nm = 'example@%d' % k
            full = None
            if nm:
                full = nm[7:] if nm.startswith('_root_.') else '.'.join(ns + [nm])
            st = pending if pending is not None else k
            starts.append((st, 'decl' if full else 'anon', full, '.'.join(ns)))
            pending = None
        elif prefre.match(line):
            if pending is None:
                pending = k
            if line.startswith('/--') and '-/' not in line:
                incomment = True
        else:
            if pending is not None:
                starts.append((pending, 'struct', None, '.'.join(ns)))
                pending = None
            starts.append((k, 'struct', None, '.'.join(ns)))
            if line.startswith('/-') and '-/' not in line:
                incomment = True
            if mn:
                ns.append(mn.group(1))
            elif me and ns and ns[-1].split('.')[-1] == me.group(1).split('.')[-1]:
                ns.pop()
    starts.sort()
    it = []
    for j, (st, kind, full, nsv) in enumerate(starts):
        en = starts[j + 1][0] if j + 1 < len(starts) else len(L)
        it.append((kind, full, st, en, nsv))
    items[m] = (L, it)
    opens[m] = op

decls = collections.defaultdict(list)
for m, (L, it) in items.items():
    for j, x in enumerate(it):
        if x[0] == 'decl':
            decls[x[1]].append((m, j))
bylast = collections.defaultdict(list)
nsset = set()
for n in decls:
    p = n.split('.')
    bylast[p[-1]].append(n)
    for k in range(1, len(p)):
        nsset.add('.'.join(p[:k]))
        nsset.add(p[k - 1])
tok = re.compile(r"\.?[A-Za-z_Ͱ-Ͽ][\w.'!?₀-₉Ͱ-Ͽ]*")


def resolve(t, m, curns):
    out = set()
    parts = curns.split('.') if curns else []
    for p in ['.'.join(parts[:k]) for k in range(len(parts) + 1)] + list(opens[m]):
        c = (p + '.' + t) if p else t
        if c in decls:
            out.add(c)
    if '.' in t:
        comps = t.split('.')
        for k in range(1, len(comps)):
            out |= resolve(comps[k - 1] if k == 1 else '.'.join(comps[:k]), m, curns)
        if comps[0] not in nsset:
            for c in comps[1:]:
                out |= set(bylast.get(c, []))
    return out


keep = set()
work = [x for d in TARGETS for x in decls[d]]
for m in allm:
    for j, x in enumerate(items[m][1]):
        if x[0] == 'anon':
            work.append((m, j))
while work:
    m, j = work.pop()
    if (m, j) in keep:
        continue
    keep.add((m, j))
    L, it = items[m]
    kind, full, st, en, nsv = it[j]
    if kind == 'struct':
        continue
    text = '\n'.join(L[st:en])
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    for t in set(tok.findall(text)):
        cs = resolve(t.lstrip('.').rstrip('.'), m, nsv)
        if t.startswith('.'):
            for c in t.strip('.').split('.'):
                cs |= set(bylast.get(c, []))
        for c in cs:
            for (mm, jj) in decls[c]:
                # one-letter names are nearly always local variables
                if len(c.split('.')[-1]) <= 1 and mm != m:
                    continue
                if mm in trans(m):
                    work.append((mm, jj))

# the additive_combination tactic file is kept only by its own syntax; no kept proof uses it
EXCLUDE = {'LeanLab.PNTPort.StrongPNT.Tactic.AdditiveCombination'}
RENAMED = {'Mathlib.Tactic.LinearCombinationPrime': 'Mathlib.Tactic.LinearCombination'}
files = sorted({m for (m, j) in keep if items[m][1][j][0] == 'decl'} - EXCLUDE)
fileset = set(files)
os.makedirs(OUT, exist_ok=True)
rows = []
tot_src = tot_out = 0


def all_imports(m):
    r = []
    for line in open(path(m)):
        mm = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)', line)
        if mm:
            r.append(mm.group(1))
    return r


def expand(mod):
    # a dropped module is replaced by what it imports, kept modules and Mathlib modules
    if not mod.startswith('LeanLab'):
        return [RENAMED.get(mod, mod)]
    if mod in fileset:
        return [mod.replace('LeanLab.', 'SchoenfeldPort.', 1)]
    out = []
    for i in all_imports(mod):
        for x in expand(i):
            if x not in out:
                out.append(x)
    return out


def fix_import(mt):
    return '\n'.join('import ' + x for x in expand(mt.group(2)))


keptns = set()
keptdecls = {items[mm][1][j][1] for (mm, j) in keep if items[mm][1][j][0] == 'decl' and mm in fileset}
for (mm, j) in keep:
    x = items[mm][1][j]
    if x[0] == 'decl' and mm in fileset:
        p = x[1].split('.')
        for k in range(1, len(p)):
            keptns.add('.'.join(p[:k]))


def prune_open(mt):
    toks = mt.group(2).split()
    good = [t for t in toks if not t.startswith('LeanLab.') or t in keptns]
    if not good:
        return ''
    names = mt.group(3) or ''
    if names and good and good[-1].startswith('LeanLab.'):
        kept_names = [x for x in names.strip()[1:-1].split() if good[-1] + '.' + x in keptdecls]
        names = ''
        if kept_names:
            names, w = ' (', len(mt.group(1)) + len(' '.join(good)) + 2
            for x in kept_names:
                if w + len(x) > 98:
                    names, w = names.rstrip() + '\n  ', 2
                names, w = names + x + ' ', w + len(x) + 1
            names = names.rstrip() + ')'
        if not kept_names and len(good) == 1:
            return ''
    return mt.group(1) + ' '.join(good) + names + (mt.group(4) or '')


for m in files:
    L, it = items[m]
    out = []
    for j, (kind, full, st, en, nsv) in enumerate(it):
        if kind == 'decl' and (m, j) not in keep:
            continue
        out.extend(L[st:en])
    s = '\n'.join(out)
    s = re.sub(r'^(open\s+(?:scoped\s+)?)([^(\n]*?)(\s*\([^)]*\))?([ \t]+in)?[ \t]*$', prune_open, s, flags=re.M)
    s = re.sub(r'^(public\s+)?(?:meta\s+)?import\s+(\S+)', fix_import, s, flags=re.M)
    s = re.sub(r'^module\s*$', '', s, flags=re.M)
    s = re.sub(r'^@\[expose\]\s+public\s+section\s*$', '', s, flags=re.M)
    s = re.sub(r'^public\s+meta\s+section\s*$', '', s, flags=re.M)
    s = re.sub(r'^public\s+section\s*$', '', s, flags=re.M)
    s = s.replace('LeanLab.', 'SchoenfeldPort.')
    s = re.sub(r'\n{3,}', '\n\n', s).lstrip('\n')
    dst = os.path.join(OUT, m.replace('LeanLab.', 'SchoenfeldPort.', 1).replace('.', '/') + '.lean')
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if not os.path.exists(dst) or open(dst).read() != s + '\n':
        open(dst, 'w').write(s + '\n')
    nk = sum(1 for (mm, j) in keep if mm == m and it[j][0] == 'decl')
    nd = sum(1 for x in it if x[0] == 'decl')
    n_out = s.count('\n') + 1
    rows.append((m, len(L), n_out, nk, nd))
    tot_src += len(L)
    tot_out += n_out
for r in rows:
    print('%-55s src %5d  kept %5d  decls %3d/%3d' % r)
print('%d files, source lines %d, after strip %d' % (len(rows), tot_src, tot_out))
print('dropped files:', sorted(allm - fileset))
