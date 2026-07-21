-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L2.GradeAlgebra
/-!
# Lattice grade algebras — `grade = Low <= High` (ET-5 instance)

The generic theorem: **every bounded distributive lattice is a grade
algebra**, with

* `add` = `meet` (joining two uses takes the lower bound of what both allow),
* `mul` = `join` (sequential composition escalates),
* `zero` = `⊤` (an unused assumption constrains nothing),
* `one` = `⊥`,
* `le a b` = `meet a b = a` (the induced lattice order).

Instantiated at the two-point information-flow lattice `Low ≤ High`.
The order-theoretic facts (idempotence, the meet/join characterizations of
the order, monotonicity of both operations) are derived from the absorption
laws in the classical way — nothing is assumed beyond the lattice axioms.
-/

namespace Systemet.L2

/-- A bounded distributive lattice, self-contained (no mathlib). -/
class BoundedDistLattice (L : Type) where
  meet : L → L → L
  join : L → L → L
  top  : L
  bot  : L
  meet_assoc : ∀ a b c : L, meet (meet a b) c = meet a (meet b c)
  meet_comm  : ∀ a b : L, meet a b = meet b a
  join_assoc : ∀ a b c : L, join (join a b) c = join a (join b c)
  join_comm  : ∀ a b : L, join a b = join b a
  absorb_meet : ∀ a b : L, meet a (join a b) = a
  absorb_join : ∀ a b : L, join a (meet a b) = a
  meet_top   : ∀ a : L, meet a top = a
  join_bot   : ∀ a : L, join a bot = a
  /-- Distributivity of `join` over `meet` (the direction `mul`-over-`add`
      that the grade-algebra laws need). -/
  join_distrib : ∀ a b c : L, join a (meet b c) = meet (join a b) (join a c)

namespace BoundedDistLattice

variable {L : Type} [BoundedDistLattice L]

theorem meet_idem (a : L) : meet a a = a := by
  have h := absorb_meet a (meet a a)
  rw [absorb_join] at h
  exact h

theorem join_idem (a : L) : join a a = a := by
  have h := absorb_join a (meet a a)
  rw [meet_idem] at h
  rw [meet_idem] at h
  exact h

theorem join_top (a : L) : join a top = top := by
  have h := absorb_join top a
  rw [meet_comm, meet_top] at h
  rw [join_comm]
  exact h

/-- The two order characterizations agree: `meet a b = a ↔ join a b = b`. -/
theorem le_iff_join {a b : L} : meet a b = a ↔ join a b = b := by
  constructor
  · intro h
    have := absorb_join b (meet b a)
    calc join a b = join (meet a b) b := by rw [h]
      _ = join b (meet b a) := by rw [join_comm, meet_comm]
      _ = b := absorb_join b a
  · intro h
    calc meet a b = meet a (join a b) := by rw [h]
      _ = a := absorb_meet a b

/-- AC shuffle for `meet`: `(a∧c)∧(b∧d) = (a∧b)∧(c∧d)`. -/
theorem meet_ac (a b c d : L) :
    meet (meet a c) (meet b d) = meet (meet a b) (meet c d) := by
  rw [meet_assoc, meet_assoc]
  congr 1
  rw [← meet_assoc, ← meet_assoc]
  congr 1
  exact meet_comm c b

/-- AC shuffle for `join`. -/
theorem join_ac (a b c d : L) :
    join (join a c) (join b d) = join (join a b) (join c d) := by
  rw [join_assoc, join_assoc]
  congr 1
  rw [← join_assoc, ← join_assoc]
  congr 1
  exact join_comm c b

/-- Every bounded distributive lattice is an L2 grade algebra. -/
instance grade : GradeAlgebra L where
  add := meet
  mul := join
  zero := top
  one := bot
  le a b := meet a b = a
  add_assoc := meet_assoc
  add_comm := meet_comm
  add_zero := meet_top
  mul_assoc := join_assoc
  one_mul := fun a => by rw [join_comm]; exact join_bot a
  mul_one := join_bot
  zero_mul := fun a => by rw [join_comm]; exact join_top a
  mul_zero := join_top
  left_distrib := join_distrib
  right_distrib := fun a b c => by
    rw [join_comm, join_distrib, join_comm, join_comm c]
  le_refl := meet_idem
  le_trans := fun a b c hab hbc => by
    calc meet a c = meet (meet a b) c := by rw [hab]
      _ = meet a (meet b c) := meet_assoc a b c
      _ = meet a b := by rw [hbc]
      _ = a := hab
  le_antisymm := fun a b hab hba => by
    calc a = meet a b := hab.symm
      _ = meet b a := meet_comm a b
      _ = b := hba
  add_mono := fun a b c d hab hcd => by
    calc meet (meet a c) (meet b d) = meet (meet a b) (meet c d) := meet_ac a b c d
      _ = meet a c := by rw [hab, hcd]
  mul_mono := fun a b c d hab hcd => by
    have hab' := le_iff_join.mp hab
    have hcd' := le_iff_join.mp hcd
    apply le_iff_join.mpr
    calc join (join a c) (join b d) = join (join a b) (join c d) := join_ac a b c d
      _ = join b d := by rw [hab', hcd']

end BoundedDistLattice

/-- The two-point information-flow lattice: `Low ≤ High`. -/
inductive Level : Type where
  | low  : Level
  | high : Level
deriving DecidableEq, Repr

namespace Level

/-- `meet` (with `Low` as bottom-of-information, `High` as top). -/
def meet : Level → Level → Level
  | .high, .high => .high
  | _,     _     => .low

def join : Level → Level → Level
  | .low, .low => .low
  | _,    _    => .high

instance lattice : BoundedDistLattice Level where
  meet := meet
  join := join
  top := .high
  bot := .low
  meet_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  meet_comm  := by intro a b; cases a <;> cases b <;> rfl
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_comm  := by intro a b; cases a <;> cases b <;> rfl
  absorb_meet := by intro a b; cases a <;> cases b <;> rfl
  absorb_join := by intro a b; cases a <;> cases b <;> rfl
  meet_top := by intro a; cases a <;> rfl
  join_bot := by intro a; cases a <;> rfl
  join_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- `Level` is a grade algebra — via the generic theorem, not a bespoke proof.
    This is ET-5's "same rules, different algebra" in one line. -/
example : GradeAlgebra Level := inferInstance

end Level

end Systemet.L2
