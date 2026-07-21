-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L2.GradeAlgebra
/-!
# The Cost grade algebra — `grade = Cost * Nat` (ET-5 instance)

Tropical-style cost accounting over `ℕ ∪ {∞}`:

* `add` = `min` — joining two uses keeps the cheaper bound;
* `mul` = numeric `+` — sequential composition accumulates cost;
* `zero` = `∞` — an unused assumption consumes no budget (identity for `min`,
  absorbing for `+`);
* `one` = `0` — a single direct use is free at this layer;
* `le` — `fin m ≤ fin n ↔ m ≤ n`, and everything is `≤ inf`.

This fixes one of the two sensible readings named in
docs/theory/09-grade-algebra-catalogue.adoc; the checklist there is
"verified" for exactly this reading.
-/

namespace Systemet.L2

inductive Cost : Type where
  | fin : Nat → Cost
  | inf : Cost
deriving DecidableEq, Repr

namespace Cost

/-- `Nat.min` is monotone in both arguments (`omega` treats `min` as opaque,
    so this is discharged by unfolding to the conditional first). -/
private theorem nat_min_le_min {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) :
    Nat.min a c ≤ Nat.min b d := by
  simp only [Nat.min_def]
  split <;> split <;> omega

/-- Join = min: `inf` is the identity. -/
def add : Cost → Cost → Cost
  | .fin m, .fin n => .fin (Nat.min m n)
  | .inf,   b      => b
  | a,      .inf   => a

/-- Sequential composition = plus: `inf` absorbs. -/
def mul : Cost → Cost → Cost
  | .fin m, .fin n => .fin (m + n)
  | _,      _      => .inf

/-- The natural cost order, with `inf` on top. -/
def le : Cost → Cost → Prop
  | .fin m, .fin n => m ≤ n
  | _,      .inf   => True
  | .inf,   .fin _ => False

instance : (a b : Cost) → Decidable (le a b)
  | .fin _, .fin _ => inferInstanceAs (Decidable (_ ≤ _))
  | .fin _, .inf   => inferInstanceAs (Decidable True)
  | .inf,   .inf   => inferInstanceAs (Decidable True)
  | .inf,   .fin _ => inferInstanceAs (Decidable False)

instance grade : GradeAlgebra Cost where
  add := add
  mul := mul
  zero := .inf
  one := .fin 0
  le := le
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> simp [add, Nat.min_assoc]
  add_comm := by
    intro a b
    cases a <;> cases b <;> simp [add, Nat.min_comm]
  add_zero := by intro a; cases a <;> rfl
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> simp [mul, Nat.add_assoc]
  one_mul := by intro a; cases a <;> simp [mul]
  mul_one := by intro a; cases a <;> simp [mul]
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by
    intro a b c
    cases a <;> cases b <;> cases c <;> simp [mul, add, Nat.add_min_add_left]
  right_distrib := by
    intro a b c
    cases a <;> cases b <;> cases c <;> simp [mul, add, Nat.add_min_add_right]
  le_refl := by intro a; cases a <;> simp [le]
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [le] <;> omega
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [le] <;> omega
  add_mono := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, add] <;>
      first
        | omega
        | (apply nat_min_le_min <;> assumption)
        | (exact Nat.le_trans (Nat.min_le_left _ _) (by assumption))
        | (exact Nat.le_trans (Nat.min_le_right _ _) (by assumption))
  mul_mono := by
    intro a b c d hab hcd
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [le, mul] <;> omega

end Cost

end Systemet.L2
