-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L2.GradeAlgebra
/-!
# The Affine grade algebra — `grade = Affine` (ET-5 instance)

Carrier `{0, 1, ω}`: unused / exactly-once-available / unrestricted.
This is AffineScript's usage algebra (README §"Disciplines as a one-line
change of algebra"). The carrier is finite, so every law closes by `decide`.
-/

namespace Systemet.L2

inductive Affine : Type where
  | zero  : Affine
  | one   : Affine
  | omega : Affine
deriving DecidableEq, Repr

namespace Affine

/-- Context join: a second use of anything makes it unrestricted. -/
def add : Affine → Affine → Affine
  | .zero,  b      => b
  | a,      .zero  => a
  | _,      _      => .omega

/-- Scaling: `zero` absorbs; `one` is neutral; `ω·ω = ω`. -/
def mul : Affine → Affine → Affine
  | .zero,  _      => .zero
  | _,      .zero  => .zero
  | .one,   b      => b
  | a,      .one   => a
  | .omega, .omega => .omega

/-- Subusage as a decidable Bool: `ω` accepts anything; otherwise exact. -/
def leB : Affine → Affine → Bool
  | .zero,  .zero  => true
  | .one,   .one   => true
  | _,      .omega => true
  | _,      _      => false

def le (a b : Affine) : Prop := leB a b = true

instance (a b : Affine) : Decidable (le a b) :=
  inferInstanceAs (Decidable (leB a b = true))

/- Core Lean has no `Fintype`, so quantified goals over `Affine` are closed
   by exhaustive case analysis rather than `decide`. Every case computes. -/
instance grade : GradeAlgebra Affine where
  add := add
  mul := mul
  zero := .zero
  one := .one
  le := le
  add_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm      := by intro a b; cases a <;> cases b <;> rfl
  add_zero      := by intro a; cases a <;> rfl
  mul_assoc     := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul       := by intro a; cases a <;> rfl
  mul_one       := by intro a; cases a <;> rfl
  zero_mul      := by intro a; cases a <;> rfl
  mul_zero      := by intro a; cases a <;> rfl
  left_distrib  := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  le_refl       := by intro a; cases a <;> rfl
  le_trans      := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [le, leB]
  le_antisymm   := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [le, leB]
  add_mono      := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, leB, add]
  mul_mono      := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, leB, mul]

end Affine

end Systemet.L2
