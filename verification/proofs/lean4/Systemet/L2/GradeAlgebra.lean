-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
/-!
# The L2 grade-algebra contract (ET-4)

This class IS the precise statement of obligation ET-4
(`docs/theory/OBLIGATIONS.adoc`): the laws a candidate grade algebra must
satisfy to be admissible at L2. An instance proof of this class for a
candidate `R` is the mechanical admissibility check.

Reading of the components (docs/theory/03-l2-grades.adoc):
* `zero` — the grade of an unused assumption
* `one`  — the grade of a single direct use
* `add`  — context join (combining two uses of one assumption)
* `mul`  — sequential composition / scaling under a graded modality
* `le`   — subusage: `le r s` means grade `r` may stand where `s` is demanded

Deliberately self-contained: no mathlib, so nothing here can drift with an
external library's class hierarchy.
-/

namespace Systemet.L2

/-- An ordered semiring: the admissibility contract for an L2 grade algebra. -/
class GradeAlgebra (R : Type) where
  add  : R → R → R
  mul  : R → R → R
  zero : R
  one  : R
  le   : R → R → Prop
  /-- `add` is a commutative monoid with unit `zero`. -/
  add_assoc     : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm      : ∀ a b : R, add a b = add b a
  add_zero      : ∀ a : R, add a zero = a
  /-- `mul` is a monoid with unit `one`, absorbing at `zero`. -/
  mul_assoc     : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul       : ∀ a : R, mul one a = a
  mul_one       : ∀ a : R, mul a one = a
  zero_mul      : ∀ a : R, mul zero a = zero
  mul_zero      : ∀ a : R, mul a zero = zero
  /-- `mul` distributes over `add` on both sides. -/
  left_distrib  : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)
  /-- `le` is a partial order. -/
  le_refl       : ∀ a : R, le a a
  le_trans      : ∀ a b c : R, le a b → le b c → le a c
  le_antisymm   : ∀ a b : R, le a b → le b a → a = b
  /-- The operations are monotone with respect to `le`. -/
  add_mono      : ∀ a b c d : R, le a b → le c d → le (add a c) (add b d)
  mul_mono      : ∀ a b c d : R, le a b → le c d → le (mul a c) (mul b d)

namespace GradeAlgebra

variable {R : Type} [GradeAlgebra R]

/-- `zero + a = a` — derived, so instances need not prove both unit laws. -/
theorem zero_add (a : R) : add zero a = a := by
  rw [add_comm]; exact add_zero a

end GradeAlgebra

end Systemet.L2
