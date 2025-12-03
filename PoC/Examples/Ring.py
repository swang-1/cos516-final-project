import sys
from pathlib import Path

sys.path.append(str(Path(__file__).parent.parent))

import csv
import z3
from InvariantSearch import *
from lib import *

'''
Ring leader election example for invariant generation
'''

# The uninterpreted sort to represent nodes
Node = z3.DeclareSort('node')

w = z3.Const('w', Node)
x = z3.Const('x', Node)
y = z3.Const('y', Node)
z = z3.Const('z', Node)


# ================ Relation definitions ================

leader = z3.Function('leader', Node, z3.BoolSort())
pending = z3.Function('pending', Node, Node, z3.BoolSort())

# primed functions to represent state after a transition
leader_p = z3.Function('leader_p', Node, z3.BoolSort())
pending_p = z3.Function('pending_p', Node, Node, z3.BoolSort())

# Total ordering relation
le = z3.Function('le', Node, Node, z3.BoolSort())

# Ring topology relation
btw = z3.Function('btw', Node, Node, Node, z3.BoolSort())


# ================ Total ordering constraints ================

tot = []

# Reflexivity
tot.append(z3.ForAll([x], le(x, x))) 

# transitivity
tot.append(z3.ForAll([x, y, z], z3.Implies( 
    z3.And(le(x, y), le(y, z)), le(x, z)
)))

# Antisymmetry
tot.append(z3.ForAll([x, y], z3.Implies(
    z3.And(le(x, y), le(y, x)), x == y 
)))

# Totality
tot.append(z3.ForAll([x, y], z3.Or(le(x, y), le(y, x))))


# ================ Ring topology constraints ================

between = []

# Forms a ring
between.append(z3.ForAll([x, y, z], z3.Implies(btw(x, y, z), btw(y, z, x))))

# Transitivity
between.append(z3.ForAll([w, x, y, z], z3.Implies(
    z3.And(btw(w, x, y), btw(w, y, z)), btw(w, x, z)
)))

# Directional constraint
between.append(z3.ForAll([w, x, y], z3.Implies(
    btw(w, x, y), z3.Not(btw(w, y, x))
)))

# Totality
between.append(z3.ForAll([w, x, y], z3.Or(
    btw(w, x, y), btw(w, y, x), w == x, w == y, x == y
)))


# ================ Initial state constraints ================

leader_init = z3.ForAll([x], leader(x) == z3.BoolVal(False))
pending_init = z3.ForAll([x, y], pending(x, y) == z3.BoolVal(False))
init = [leader_init, pending_init]


# ================ State transition formulas ================

n = z3.Const('n', Node)
next = z3.Const('next', Node)

def update_pending(u, v):
    return z3.ForAll([x, y],
        pending_p(x, y) == z3.If(
            z3.And(x == u, y == v),
            z3.BoolVal(True),
            pending(x, y)
        ))

def btw_precond(u, v):
    return z3.ForAll([z], z3.And(
            u != v,
            z3.Implies(z3.And(z != u, z != v), btw(u, v, z) == z3.BoolVal(True))
        ))

leader_unchanged = z3.ForAll([x], leader_p(x) == leader(x))

send = z3.Exists([n, next], z3.And(
    btw_precond(n, next), 
    leader_unchanged, 
    update_pending(n, next)))

sender = z3.Const('sender', Node)

def pending_nondet(u, v):
    return z3.ForAll([x, y], z3.Implies(
        z3.Or(x != u, y != v),
        pending_p(x, y) == pending(x, y)
    ))

def pending_forward(nondet1, nondet2, update1, update2):
    return z3.ForAll([x, y], z3.And(
        z3.Implies(
            z3.And(x == update1, y == update2),
            pending_p(x, y) == z3.BoolVal(True)
        ),
        z3.Implies(
            z3.And(
                z3.Or(x != nondet1, y != nondet2),
                z3.Or(x != update1, y != update2)
            ),
            pending_p(x, y) == pending(x, y)
        )
    ))

recv = z3.Exists([sender, n, next], z3.And(
    btw_precond(n, next),
    pending(sender, n) == z3.BoolVal(True),
    z3.ForAll([x], leader_p(x) == z3.If(
        sender == n,
        z3.If(x == n, z3.BoolVal(True), leader(x)),
        leader(x)
    )),
    z3.If(sender == n,
          pending_nondet(sender, n),
          z3.If(le(n, sender),
                pending_forward(n, sender, sender, next),
                pending_nondet(sender, n)))))


# ================ Package for use with invariant search algorithm ================

sorts = [Node]

leader_rel = Relation(leader, [Node], leader_p, protocol=True)
pending_rel = Relation(pending, [Node, Node], pending_p, protocol=True)
le_rel = Relation(le, [Node, Node], unique_args=True)
btw_rel = Relation(btw, [Node, Node, Node], unique_args=True)
relations = [leader_rel, pending_rel, le_rel, btw_rel]

qvars = [w, x, y, x]

trs = [send, recv]
axioms = tot + between

# First counterexample, when trying to verify just the safety property
# with no additional invariants:
#
# sort node = #[node0, node1]
# n = node0
# next = node1
# sender = node0
# st.pending(node0, node0) = true
# st'.leader(node0) = true
# tot.le(node0, node0) = true
# tot.le(node0, node1) = true
# tot.le(node1, node1) = true
node0 = z3.Const('node0', Node)
node1 = z3.Const('node1', Node)

cex1 = [
    le(node0, node0) == z3.BoolVal(True),
    le(node0, node1) == z3.BoolVal(True),
    le(node1, node1) == z3.BoolVal(True),
    pending(node0, node0) == z3.BoolVal(True),
    leader_p(node0) == z3.BoolVal(True)
]

invariants = generate_invariants(qvars, relations, 2, 1)

out = invariant_search(axioms, init, trs, invariants, cex1, debug=False)

with open('ring_invariants.csv', 'w', newline='') as csvfile:
    writer = csv.writer(csvfile)
    for inv in out:
        writer.writerow([inv.formula()])