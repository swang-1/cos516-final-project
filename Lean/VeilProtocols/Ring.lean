import Veil

-- From https://github.com/verse-lab/veil/blob/main/Examples/IvyBench/Ring.lean

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Prop
relation pending : node -> node -> Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
}

action send (n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

action recv (sender n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := *
  if (sender = n) then
    leader n := True
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := True
}

safety [single_leader] leader L → le N L

-- ====== The invariants for the original example ======
-- invariant pending S D ∧ btw S N D → le N S
-- invariant pending L L → le N L

-- ====== Invariants from running search ======
invariant btw W Y X ∧ pending Y W → ¬ le Y X
invariant btw W Y X ∧ pending X X → ¬ le X Y
invariant btw W Y X ∧ pending W W → ¬ le W Y
invariant ¬ le W X ∧ ¬ le Y X → ¬ pending X X

#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

#check_invariants

end Ring
