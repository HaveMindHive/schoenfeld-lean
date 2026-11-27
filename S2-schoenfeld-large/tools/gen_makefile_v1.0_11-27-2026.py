"""Write build/Makefile: one olean per ported module, compiled against the built RH repo.
usage: python3 -I gen_makefile_v1.0_11-27-2026.py PORT_DIR"""
import os, re, sys, glob
PORT = os.path.abspath(sys.argv[1])
REPO = os.path.expanduser('~/Library/CloudStorage/OneDrive-rkfleming/HaveMindHive/'
                          'riemann-hypothesis-community_v1.0_11-27-2026/repo')
SRC, B = PORT + '/src', PORT + '/build'
lp = [B, REPO + '/.lake/build/lib/lean'] + sorted(glob.glob(REPO + '/.lake/packages/*/.lake/build/lib/lean'))
LEAN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin/lean')
lp.append(os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/lib/lean'))
mods = {}
for f in glob.glob(SRC + '/**/*.lean', recursive=True):
    m = os.path.relpath(f, SRC)[:-5].replace('/', '.')
    deps = re.findall(r'^import\s+(SchoenfeldPort\.\S+)', open(f).read(), flags=re.M)
    mods[m] = deps
def ol(m): return B + '/' + m.replace('.', '/') + '.olean'
out = ['LEAN_PATH := ' + ':'.join(lp), 'export LEAN_PATH', '.DELETE_ON_ERROR:', 'all: ' + ' '.join(ol(m) for m in sorted(mods)), '']
for m, deps in sorted(mods.items()):
    src = SRC + '/' + m.replace('.', '/') + '.lean'
    o = ol(m)
    out.append('%s: %s %s' % (o, src, ' '.join(ol(d) for d in deps)))
    out.append('\t@mkdir -p $(dir $@)')
    out.append('\t@echo "BUILD %s"' % m)
    out.append('\t@cd %s && (/usr/bin/time -p %s -j1 --tstack=400000 --root=%s -o %s -i %s %s > %s.log 2>&1 && echo "OK %s") || (echo "FAIL %s"; head -c 4000 %s.log; false)'
               % (REPO, LEAN, SRC, o, o[:-6] + '.ilean', src, o[:-6], m, m, o[:-6]))
    out.append('')
os.makedirs(B, exist_ok=True)
open(B + '/Makefile', 'w').write('\n'.join(out))
print(len(mods), 'modules')
