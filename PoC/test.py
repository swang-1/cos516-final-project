import z3
import Examples.Ring as Ring
from InvariantSearch import generate_invariants
import lib

def dest_app_and_relation():
    node = Ring.Node
    x = Ring.x
    leader = Ring.leader_rel

    app = lib.App(leader, [x])
    print(f"instantiation: {app.instantiate()}")

def test_generate_invariants_depth1():
    res = generate_invariants(Ring.qvars, Ring.sorts, Ring.relations, 1)
    for lhs, rhs in res:
        print(f"lhs:{[app.instantiate() for app in lhs]}, rhs: {[app.instantiate() for app in rhs]}")

if __name__ == "__main__":
    # dest_app_and_relation()
    test_generate_invariants_depth1()