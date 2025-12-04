import sys
from pathlib import Path

sys.path.append(str(Path(__file__).parent.parent))

import csv
import z3
from InvariantSearch import *
from lib import *

# The uninterpreted sort to represent nodes
Node = z3.DeclareSort('node')

startNode = z3.Const('startNode', Node)

w = z3.Const('w', Node)
x = z3.Const('x', Node)
y = z3.Const('y', Node)
z = z3.Const('z', Node)


# ================ Relation definitions ================

message = z3.Function('message', Node, Node, z3.BoolSort())
lock = z3.Function('lock', Node, z3.BoolSort())

# primed functions to represent state after a transition
message_p = z3.Function('message_p', Node, Node, z3.BoolSort())
lock_p = z3.Function('lock_p', Node, z3.BoolSort())


# ================ Initial state constraints ================

message_init = z3.ForAll([x, y], message(x, y) == z3.BoolVal(False))
lock_init = z3.ForAll(x, lock(x) == (x == startNode))

init = [message_init, lock_init]

# ================ State transition formulas ================

def update_message(u, v, b):
    return z3.ForAll([x, y], 
                     message_p(x, y) == z3.If(
                         z3.And(x == u, y == v),
                         z3.BoolVal(b),
                         message(x, y)
                     ))

def update_lock(u, b):
    return z3.ForAll(x, lock_p(x) == z3.If(
                        x == u,
                        z3.BoolVal(b),
                        lock(x)
                     ))

src = z3.Const('src', Node)
dst = z3.Const('dst', Node)

# send = z3.Exists([src, dst], z3.And(
#     lock(src) == z3.BoolVal(True),
#     update_message(src, dst, True),
#     update_lock(src, False)
# ))
send = z3.And(
    lock(src) == z3.BoolVal(True),
    update_message(src, dst, True),
    update_lock(src, False)
)

# recv = z3.Exists([src, dst], z3.And(
#     message(src, dst) == z3.BoolVal(True),
#     update_message(src, dst, False),
#     update_lock(dst, True)
# ))
recv = z3.And(
    message(src, dst) == z3.BoolVal(True),
    update_message(src, dst, False),
    update_lock(dst, True)
)


# ================ Package for use with invariant search algorithm ================

message_rel = Relation(message, [Node, Node], message_p, protocol=True)
lock_rel = Relation(lock, [Node], lock_p, protocol=True)

relations = [lock_rel, message_rel]
qvars = [w, x, y, z]
axioms = []
trs = [send, recv]

# Counterexample:
# recv_tr_mutex:
# interpreted sort Bool
# sort node = #[node0, node1]
# dst = node0
# src = node0
# st.lock(node1) = true
# st.message(node0, node0) = true
# st.startNode = node1
# st'.lock(node0) = true
# st'.lock(node1) = true
# st'.startNode = node1
node0 = z3.Const('node0', Node)
node1 = z3.Const('node1', Node)
cex1 = [
    node1 == startNode,
    lock(node1) == z3.BoolVal(True),
    message(node0, node0) == z3.BoolVal(True),
    lock_p(node0) == z3.BoolVal(True),
    lock_p(node1) == z3.BoolVal(True)
]

no_msg_if_lock = z3.ForAll([w, x, y], z3.Implies(
    lock(w) == z3.BoolVal(True),
    message(x, y) == z3.BoolVal(False)
))


if __name__ == "__main__":
    invariants = generate_invariants(qvars, relations, 2)

    out, success = invariant_search(axioms, init, trs, invariants, cex1, debug=True)

    with open('lock_invariants.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([f"Counterexample elimination succeeded? {success}"])
        for inv in out:
            writer.writerow([inv.formula()])

    # Test if the counterexample is written correctly
    # s = z3.Solver()
    # s.add(cex1)
    # s.add(no_msg_if_lock)
    # print(s.check())

    # inv = z3.ForAll([z, y], z3.Implies(
    #     z3.And(z3.Not(message(y, z)), z3.Not(message(z, z))),
    #     z3.And(z3.Not(message(y, z)), z3.Not(message(z, y)))
    # ))
    # inv_p = z3.ForAll([z, y], z3.Implies(
    #     z3.And(z3.Not(message_p(y, z)), z3.Not(message_p(z, z))),
    #     z3.And(z3.Not(message_p(y, z)), z3.Not(message_p(z, y)))
    # ))
    # s.add(inv, send)
    # s.add(z3.Not(inv_p))
    # print(s.check())
    # print(z3.prove(z3.Implies(z3.And(init), inv)))
    # print(z3.prove(z3.Implies(z3.And(inv, send), inv_p)))




