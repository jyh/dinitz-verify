"""Two independent checks of this repository, in one script.

1. A dependency-free Python brute force of the instance (conservation, d_max, fractional
   cost, exhaustive walk enumeration, all 8 routings) -- a sanity oracle only; the Lean
   files are the referee.
2. The Lean gates: `lake build`, an axiom audit of every theorem named in the
   `#print axioms` block of `Submission.lean`, and the statement-identity bridge
   `example : (¬ DGGCostConjectureFull ℚ) := Submission.goemans_cost_conjecture_false`,
   which type-checks only if the submission proves exactly the statement that
   `Challenge.lean` states.

Usage:  python3 check.py            # everything
        python3 check.py --brute    # part 1 only (no Lean toolchain needed)
"""

import itertools
import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.abspath(__file__))
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# ---------------------------------------------------------------------------
# 1.  The brute force.
# ---------------------------------------------------------------------------

V=['s','u','v','w','t1','t2','t3']
# arc: (tail, head, x, c)
A={'st1':('s','t1',10,2),'st2':('s','t2',6,3),'su':('s','u',24,0),
   'ut3':('u','t3',10,2),'uv':('u','v',14,0),'vt1':('v','t1',5,0),
   'vw':('v','w',9,0),'wt2':('w','t2',4,0),'wt3':('w','t3',5,0)}
dem={'t1':15,'t2':10,'t3':15}; D=max(dem.values())
# conservation
for z in V:
    inn=sum(a[2] for a in A.values() if a[1]==z); out=sum(a[2] for a in A.values() if a[0]==z)
    net=out-inn
    exp = sum(dem.values()) if z=='s' else -dem.get(z,0)
    assert net==exp, (z,net,exp)
print("conservation OK; dmax =",D)
print("fractional cost =", sum(a[2]*a[3] for a in A.values()))
# enumerate ALL walks s->t by brute force up to length 8 (well past the rank bound)
def walks(x,y,maxlen=8):
    out=[]
    def go(cur,path):
        if cur==y and path: out.append(tuple(path))
        if len(path)>=maxlen: return
        for n,(t,h,_,_) in A.items():
            if t==cur: go(h,path+[n])
    go(x,[]); return out
P={t:walks('s',t) for t in dem}
for t in P: print(t, P[t])
assert all(len(P[t])==2 for t in P), "path count"
best=None; feasible=0
for c1 in P['t1']:
  for c2 in P['t2']:
    for c3 in P['t3']:
      load={n:0 for n in A}
      for t,p in (('t1',c1),('t2',c2),('t3',c3)):
          for n in set(p): load[n]+=dem[t]
      if all(load[n]<=A[n][2]+D for n in A):
          feasible+=1
          cost=sum(A[n][3]*load[n] for n in A)
          best=cost if best is None else min(best,cost)
print("capacity-good routings:",feasible,"  min unsplittable cost:",best)

if "--brute" in sys.argv:
    sys.exit(0)

# ---------------------------------------------------------------------------
# 2.  The Lean gates.
# ---------------------------------------------------------------------------

def find_lake():
    for cand in (shutil.which("lake"), os.path.expanduser("~/.elan/bin/lake")):
        if cand and os.path.exists(cand):
            return cand
    sys.exit("check.py: `lake` not found (install elan), or run `python3 check.py --brute`")

LAKE = find_lake()

def run(args, **kw):
    return subprocess.run(args, cwd=REPO, capture_output=True, text=True, **kw)

def lean_scratch(name, source):
    """Elaborate `source` against the built libraries; return its stdout."""
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, name + ".lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(source)
        r = run([LAKE, "env", "lean", "--root=" + tmp, path])
        if r.returncode != 0:
            print(r.stdout, end="")
            print(r.stderr, end="", file=sys.stderr)
            sys.exit("check.py: FAILED -- %s did not type-check" % name)
        return r.stdout

# --- build -----------------------------------------------------------------

print("\n[1/3] lake build")
r = run([LAKE, "build"])
if r.returncode != 0:
    print(r.stdout, end="")
    print(r.stderr, end="", file=sys.stderr)
    sys.exit("check.py: FAILED -- lake build")
warnings = [ln for ln in (r.stdout + r.stderr).splitlines() if "warning:" in ln]
stray = [ln for ln in warnings if not ("Challenge.lean" in ln and "sorry" in ln)]
if stray:
    print("\n".join(stray))
    sys.exit("check.py: FAILED -- unexpected warnings (only Challenge.lean's `sorry` is expected)")
print("      build OK" + ("  (expected warning: Challenge.lean's `sorry` placeholder)"
                          if warnings else ""))

# --- axioms ----------------------------------------------------------------

print("[2/3] axiom audit")
with open(os.path.join(REPO, "Submission.lean"), encoding="utf-8") as f:
    names = re.findall(r"^#print axioms (\S+)$", f.read(), re.M)
assert "goemans_cost_conjecture_false" in names, "the headline is not in the axiom block"
qualified = ["Submission." + n for n in names]
out = lean_scratch("Axioms", "import Submission\n"
                   + "".join("#print axioms %s\n" % n for n in qualified))
seen = {}
for line in out.splitlines():
    m = re.match(r"'(\S+)' depends on axioms: \[(.*)\]$", line)
    if m:
        seen[m.group(1)] = {a.strip() for a in m.group(2).split(",")}
        continue
    m = re.match(r"'(\S+)' does not depend on any axioms$", line)
    if m:
        seen[m.group(1)] = set()
        continue
    sys.exit("check.py: FAILED -- unparsed axiom line: " + line)
bad = False
for n in qualified:
    if n not in seen:
        print("      MISSING axiom report for", n); bad = True
    elif not seen[n] <= ALLOWED_AXIOMS:
        print("      EXTRA AXIOMS in %s: %s" % (n, sorted(seen[n] - ALLOWED_AXIOMS))); bad = True
if bad:
    sys.exit("check.py: FAILED -- axiom audit")
print("      %d theorems, all within [propext, Classical.choice, Quot.sound]; no sorryAx"
      % len(qualified))

# --- the statement-identity bridge -----------------------------------------

print("[3/3] statement-identity bridge")
BRIDGE = """import Submission
open DGG

-- The submission proves the challenge statement, exactly: `Challenge.lean` and
-- `Submission.lean` share one and the same `DGGCostConjectureFull` constant, so this
-- `example` type-checks only if the proof discharges the stated Prop verbatim.
example : (¬ DGGCostConjectureFull ℚ) := Submission.goemans_cost_conjecture_false

-- ... and the theorem `Challenge.lean` states is that same Prop, not something adjacent.
example : (¬ DGGCostConjectureFull ℚ) := Challenge.goemans_cost_conjecture_false
"""
lean_scratch("Bridge", BRIDGE)
print("      example : (¬ DGGCostConjectureFull ℚ) := "
      "Submission.goemans_cost_conjecture_false  -- type-checks")
print("\ncheck.py: ALL CHECKS PASSED")
