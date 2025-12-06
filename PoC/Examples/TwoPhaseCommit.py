import sys
from pathlib import Path

sys.path.append(str(Path(__file__).parent.parent))

import csv
import z3
from InvariantSearch import *
from lib import *

'''
Two-Phase commit example for invariant generation
'''

# The uninterpreted sort to represent nodes
Node = z3.DeclareSort('node')

x = z3.Const('x', Node)
y = z3.Const('y', Node)


# ================ Relation definitions ================

vote_yes = z3.Function('vote_yes', Node, z3.BoolSort())
vote_no = z3.Function('vote_no', Node, z3.BoolSort())
alive = z3.Function('alive', Node, z3.BoolSort())
go_commit = z3.Function('go_commit', Node, z3.BoolSort())
go_abort = z3.Function('go_abort', Node, z3.BoolSort())
decide_commit = z3.Function('decide_commit', Node, z3.BoolSort())
decide_abort = z3.Function('decide_abort', Node, z3.BoolSort())
abort_flag = z3.Const('abort_flag', z3.BoolSort())

vote_yes_p = z3.Function('vote_yes_p', Node, z3.BoolSort())
vote_no_p = z3.Function('vote_no_p', Node, z3.BoolSort())
alive_p = z3.Function('alive_p', Node, z3.BoolSort())
go_commit_p = z3.Function('go_commit_p', Node, z3.BoolSort())
go_abort_p = z3.Function('go_abort_p', Node, z3.BoolSort())
decide_commit_p = z3.Function('decide_commit_p', Node, z3.BoolSort())
decide_abort_p = z3.Function('decide_abort_p', Node, z3.BoolSort())
abort_flag_p = z3.Const('abort_flag_p', z3.BoolSort())


# ================ Initial state constraints ================

vote_yes_init = z3.ForAll(x, vote_yes(x) == z3.BoolVal(False))
vote_no_init = z3.ForAll(x, vote_no(x) == z3.BoolVal(False))
alive_init = z3.ForAll(x, alive(x))
go_commit_init = z3.ForAll(x, go_commit(x) == z3.BoolVal(False))
go_abort_init = z3.ForAll(x, go_abort(x) == z3.BoolVal(False))
decide_commit_init = z3.ForAll(x, decide_commit(x) == z3.BoolVal(False))
decide_abort_init = z3.ForAll(x, decide_abort(x) == z3.BoolVal(False))
abort_flag_init = abort_flag == z3.BoolVal(False)

init = [vote_yes_init, vote_no_init, alive_init, go_commit_init, 
        go_abort_init, decide_commit_init, decide_abort_init, abort_flag_init]


# ================ State transition formulas ================

vote_yes_unchanged = z3.ForAll(x, vote_yes_p(x) == vote_yes(x))
vote_no_unchanged = z3.ForAll(x, vote_no_p(x) == vote_no(x))
alive_unchanged = z3.ForAll(x, alive_p(x) == alive(x))
go_commit_unchanged = z3.ForAll(x, go_commit_p(x) == go_commit(x))
go_abort_unchanged = z3.ForAll(x, go_abort_p(x) == go_abort(x))
decide_commit_unchanged = z3.ForAll(x, decide_commit_p(x) == decide_commit(x))
decide_abort_unchanged = z3.ForAll(x, decide_abort_p(x) == decide_abort(x))
abort_flag_unchanged = abort_flag_p == abort_flag

n = z3.Const('n', Node)

vote1 = z3.Exists(n, z3.And(
    alive(n),
    z3.Not(vote_no(n)),
    z3.Not(decide_commit(n)),
    z3.Not(decide_abort(n)),
    z3.ForAll(x, vote_yes_p(x) == z3.If(
        x == n, 
        z3.BoolVal(True),
        vote_yes(x)
    )),
    vote_no_unchanged,
    alive_unchanged,
    go_commit_unchanged,
    go_abort_unchanged,
    decide_commit_unchanged,
    decide_abort_unchanged,
    abort_flag_unchanged
))

vote2 = z3.Exists(n, z3.And(
    alive(n),
    z3.Not(vote_yes(n)),
    z3.Not(decide_commit(n)),
    z3.Not(decide_abort(n)),
    vote_yes_unchanged,
    z3.ForAll(x, vote_no_p(x) == z3.If(
        x == n, 
        z3.BoolVal(True),
        vote_no(x)
    )),
    alive_unchanged,
    go_commit_unchanged,
    go_abort_unchanged,
    decide_commit_unchanged,
    z3.ForAll(x, decide_abort_p(x) == z3.If(
        x == n,
        z3.BoolVal(True),
        decide_abort(x)
    )),
    abort_flag_p == z3.BoolVal(True)
))

fail = z3.Exists(n, z3.And(
    alive(n),
    vote_yes_unchanged,
    vote_no_unchanged,
    z3.ForAll(x, alive_p(x) == z3.And(x != n, alive(x))),
    go_commit_unchanged,
    go_abort_unchanged,
    decide_commit_unchanged,
    decide_abort_unchanged,
    abort_flag_p == z3.BoolVal(True)
))

go1 = z3.And(
    z3.ForAll(n, z3.Not(go_commit(n))),
    z3.ForAll(n, z3.Not(go_abort(n))),
    z3.ForAll(n, vote_yes(n)),
    vote_yes_unchanged,
    vote_no_unchanged,
    alive_unchanged,
    z3.ForAll(n, go_commit_p(n)),
    go_abort_unchanged,
    decide_commit_unchanged,
    decide_abort_unchanged,
    abort_flag_unchanged
)

go2 = z3.And(
    z3.ForAll(n, z3.Not(go_commit(n))),
    z3.ForAll(n, z3.Not(go_abort(n))),
    z3.Exists(n, z3.Or(vote_no(n), z3.Not(alive(n)))),
    vote_yes_unchanged,
    vote_no_unchanged, 
    alive_unchanged,
    go_commit_unchanged,
    z3.ForAll(n, go_abort_p(n)),
    decide_commit_unchanged,
    decide_abort_unchanged,
    abort_flag_unchanged
)

commit = z3.Exists(n, z3.And(
    alive(n),
    go_commit(n),
    vote_yes_unchanged,
    vote_no_unchanged,
    alive_unchanged,
    go_commit_unchanged,
    go_abort_unchanged,
    z3.ForAll(x, decide_commit_p(x) == z3.If(
        x == n,
        z3.BoolVal(True),
        decide_commit(x)
    )),
    decide_abort_unchanged,
    abort_flag_unchanged
))

abort = z3.Exists(n, z3.And(
    alive(n),
    go_abort(n),
    vote_yes_unchanged,
    vote_no_unchanged,
    alive_unchanged,
    go_commit_unchanged,
    go_abort_unchanged,
    decide_commit_unchanged,
    z3.ForAll(x, decide_abort_p(x) == z3.If(
        x == n,
        z3.BoolVal(True),
        decide_abort(x)
    )),
    abort_flag_unchanged
))


# ================ Package for use with invariant search algorithm ================

vote_yes_rel = Relation(vote_yes, [Node], vote_yes_p, protocol=True) 
vote_no_rel = Relation(vote_no, [Node], vote_no_p, protocol=True)
alive_rel = Relation(alive, [Node], alive_p, protocol=True)
go_commit_rel = Relation(go_commit, [Node], go_commit_p, protocol=True)
go_abort_rel = Relation(go_abort, [Node], go_abort_p, protocol=True)
decide_commit_rel = Relation(decide_commit, [Node], decide_commit_p, protocol=True)
decide_abort_rel = Relation(decide_abort, [Node], decide_abort_p, protocol=True)
abort_flag_rel = Relation(abort_flag, [], abort_flag_p, protocol=True)
eq = eq_rel(Node)

qvars = [x, y]
trs = [vote1, vote2, fail, go1, go2, commit, abort]
axioms = []
relations = [vote_yes_rel, vote_no_rel, alive_rel, go_commit_rel, go_abort_rel,
             decide_commit_rel, decide_abort_rel, abort_flag_rel, eq]

# Two Counterexamples:

# commit_tr_inv_0:
# interpreted sort Bool
# sort node = #[node0]
# n = node0
# st.alive(node0) = true
# st.go_commit(node0) = true
# st'.alive(node0) = true
# st'.decide_commit(node0) = true
# st'.go_commit(node0) = true


# abort_tr_inv_0:
# interpreted sort Bool
# sort node = #[node0]
# n = node0
# st.alive(node0) = true
# st.go_abort(node0) = true
# st'.alive(node0) = true
# st'.decide_abort(node0) = true
# st'.go_abort(node0) = true

node0 = z3.Const('node0', Node)

cex1 = [
    alive(node0),
    go_commit(node0),
    z3.Not(vote_yes(node0))
]

cex2 = [
    alive(node0),
    go_abort(node0),
    z3.Not(abort_flag)
]

# After running the above two counterexamples and passing the found invariants
# to Veil, we get the following counterexample:
# commit_tr_inv_0:
# interpreted sort Bool
# sort node = #[node0]
# n = node0
# st.abort_flag = true
# st.alive(node0) = true
# st.decide_abort(node0) = true
# st.go_commit(node0) = true
# st.vote_yes(node0) = true
# st'.abort_flag = true
# st'.alive(node0) = true
# st'.decide_abort(node0) = true
# st'.decide_commit(node0) = true
# st'.go_commit(node0) = true
# st'.vote_yes(node0) = true

cex3 = [
    abort_flag,
    alive(node0),
    decide_abort(node0),
    go_commit(node0),
    vote_yes(node0)
]

if __name__ == "__main__":
    invariants = generate_invariants(qvars, relations, 1, 2)

    # Counterexample 1
    out1, success1 = invariant_search(axioms, init, trs, invariants, cex1, debug=True)

    with open('commit_invariants1.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([f"Counterexample elimination succeeded? {success1}"])
        for inv in out1:
            writer.writerow([inv.formula()])

    # Counterexample 2
    out2, success2 = invariant_search(axioms, init, trs, invariants, cex2, debug=True)

    with open('commit_invariants2.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([f"Counterexample elimination succeeded? {success2}"])
        for inv in out2:
            writer.writerow([inv.formula()])

    # Counterexample 3
    out3, success3 = invariant_search(axioms, init, trs, invariants, cex3, debug=True)

    with open('commit_invariants3.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([f"Counterexample elimination succeeded? {success3}"])
        for inv in out3:
            writer.writerow([inv.formula()])