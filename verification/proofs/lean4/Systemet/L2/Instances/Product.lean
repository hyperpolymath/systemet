-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L2.GradeAlgebra
/-!
# The product construction — `grade = Latency x Billing` (ET-5 instance)

If `R` and `S` are grade algebras, so is `R × S`, componentwise. This is the
point of the README's `Latency x Billing` row: a composite discipline is
*composition of algebras*, not a new checker. Proven once, generically.
-/

namespace Systemet.L2

open GradeAlgebra

instance prodGrade {R S : Type} [GradeAlgebra R] [GradeAlgebra S] : GradeAlgebra (R × S) where
  add a b := (add a.1 b.1, add a.2 b.2)
  mul a b := (mul a.1 b.1, mul a.2 b.2)
  zero := (zero, zero)
  one := (one, one)
  le a b := le a.1 b.1 ∧ le a.2 b.2
  add_assoc a b c := by
    show (_, _) = (_, _)
    rw [add_assoc a.1 b.1 c.1, add_assoc a.2 b.2 c.2]
  add_comm a b := by
    show (_, _) = (_, _)
    rw [add_comm a.1 b.1, add_comm a.2 b.2]
  add_zero a := by
    show (_, _) = (_, _)
    rw [add_zero a.1, add_zero a.2]
  mul_assoc a b c := by
    show (_, _) = (_, _)
    rw [mul_assoc a.1 b.1 c.1, mul_assoc a.2 b.2 c.2]
  one_mul a := by
    show (_, _) = (_, _)
    rw [one_mul a.1, one_mul a.2]
  mul_one a := by
    show (_, _) = (_, _)
    rw [mul_one a.1, mul_one a.2]
  zero_mul a := by
    show (_, _) = (_, _)
    rw [zero_mul a.1, zero_mul a.2]
  mul_zero a := by
    show (_, _) = (_, _)
    rw [mul_zero a.1, mul_zero a.2]
  left_distrib a b c := by
    show (_, _) = (_, _)
    rw [left_distrib a.1 b.1 c.1, left_distrib a.2 b.2 c.2]
  right_distrib a b c := by
    show (_, _) = (_, _)
    rw [right_distrib a.1 b.1 c.1, right_distrib a.2 b.2 c.2]
  le_refl a := ⟨le_refl a.1, le_refl a.2⟩
  le_trans a b c hab hbc :=
    ⟨le_trans _ _ _ hab.1 hbc.1, le_trans _ _ _ hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    have h1 := le_antisymm _ _ hab.1 hba.1
    have h2 := le_antisymm _ _ hab.2 hba.2
    exact Prod.ext h1 h2
  add_mono a b c d hab hcd :=
    ⟨add_mono _ _ _ _ hab.1 hcd.1, add_mono _ _ _ _ hab.2 hcd.2⟩
  mul_mono a b c d hab hcd :=
    ⟨mul_mono _ _ _ _ hab.1 hcd.1, mul_mono _ _ _ _ hab.2 hcd.2⟩

end Systemet.L2
