import z3
import Examples.Ring as Ring
import InvariantSearch
import lib

def dest_app_and_relation():
    x = Ring.x
    leader = Ring.leader_rel

    app = lib.App(leader, [x])
    print(f"instantiation: {app.instantiate()}")

def test_combos_up_to_len_depth1():
    print("Testing `combos_up_to_len` for max_depth = 1")
    out = InvariantSearch.combos_up_to_len(["even", "eq"], 1)
    for combo in out:
        print(combo)

def test_combos_up_to_len_depth2():
    print("Testing `combos_up_to_len` for max_depth = 2")
    out = InvariantSearch.combos_up_to_len(["even", "eq"], 2)
    for combo in out:
        print(combo)

def test_generate_invariants_depth1():
    res = InvariantSearch.generate_invariants(Ring.qvars, Ring.sorts, Ring.relations, 1)
    for lhs, rhs in res:
        print(f"lhs:{[app.instantiate() for app in lhs]}, rhs: {[app.instantiate() for app in rhs]}")

if __name__ == "__main__":
    # dest_app_and_relation()
    # test_generate_invariants_depth1()
    test_combos_up_to_len_depth1()
    test_combos_up_to_len_depth2()