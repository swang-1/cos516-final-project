import Veil

-- From https://www.andrew.cmu.edu/user/bparno/papers/swiss.pdf

veil module DecentralizedLock

type node

relation message : node → node → Prop
relation lock : node → Prop

immutable individual startNode : node

#gen_state

after_init {
  message N1 N2 := False
  lock N := N = startNode
}

action send (src dst : node) = {
  require (lock src)

  message src dst := True
  lock src := False
}

action recv (src dst : node) = {
  require (message src dst)

  message src dst := False
  lock dst := True
}

safety [mutex] lock N1 ∧ lock N2 → N1 = N2

invariant [no_msg_if_lock] ¬(lock N1 ∧ message N2 N3)
invariant [one_msg_at_a_time] message N1 N2 ∧ message N3 N4 →
  N1 = N3 ∧ N2 = N4

#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

#check_invariants

end DecentralizedLock
